-- | Elaboration: surface AST to Core IR, with scope and quarantine checks.
--
-- Phase 2 moves the central rule from a heuristic into the language itself:
--
--   * @let@ computes /and/ constrains, so ordinary circuit code cannot
--     create an unconstrained value at all;
--   * @advice@ computes /without/ constraining, and is legal only inside a
--     @gadget@ block — an explicit, greppable marker that something subtle
--     is happening here.
--
-- Elaboration no longer tries to judge soundness. Phase 1 approximated it
-- with \"every advice wire must be mentioned by some assertion\", which was
-- both too weak (it accepted the forgeable @IsZero@) and, read as a
-- soundness rule, simply the wrong question. That job now belongs to
-- "Zkc.Analysis.Determinacy", which asks the right one: are the declared
-- /outputs/ a function of the inputs?
--
-- What remains here is the cheap, local check: advice that no assertion
-- mentions is dead weight the optimizer would delete, and is always a
-- mistake worth reporting at the source line.
module Zkc.Core.Elaborate (elaborate) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Zkc.Diagnostics
import Zkc.Syntax.Ast
import Zkc.Core.Ir

data St = St
  { stNext :: WireId
  , stEnv :: Map.Map String WireId
  , stNodes :: [Node]          -- ^ reversed
  , stAsserts :: [Assertion]   -- ^ reversed
  }

-- | Elaborate a circuit, or fail with a source-located diagnostic.
elaborate :: String -> Circuit -> Either Diagnostic Ir
elaborate fieldName circuit = do
  checkDuplicateParams (circParams circuit)
  let inputs = zipWith mkInput [1 ..] (circParams circuit)
      env0 = Map.fromList [ (pdName p, iiWire i) | (p, i) <- zip (circParams circuit) inputs ]
      st0 = St { stNext = 1 + length inputs, stEnv = env0, stNodes = [], stAsserts = [] }
  st <- goStmts Nothing st0 (circBody circuit)
  let ir = Ir
        { irName = circName circuit
        , irField = fieldName
        , irInputs = inputs
        , irNodes = reverse (stNodes st)
        , irAssertions = reverse (stAsserts st)
        }
  checkAdviceIsUsed ir
  Right ir
  where
    mkInput wire param = IrInput wire (pdName param) (pdVisibility param) (pdLine param)

checkDuplicateParams :: [ParamDecl] -> Either Diagnostic ()
checkDuplicateParams = go Set.empty
  where
    go _ [] = Right ()
    go seen (p:ps)
      | pdName p `Set.member` seen =
          Left $ diagAt (pdLine p) ("duplicate parameter '" ++ pdName p ++ "'")
      | otherwise = go (Set.insert (pdName p) seen) ps

-- | The first argument is the enclosing gadget, if any.
goStmts :: Maybe String -> St -> [Stmt] -> Either Diagnostic St
goStmts gadget = go
  where
    go st [] = Right st
    go st (s:ss) = goStmt gadget st s >>= \st' -> go st' ss

goStmt :: Maybe String -> St -> Stmt -> Either Diagnostic St
goStmt gadget st stmt = case stmt of
  SLet name body line -> do
    ensureFree st name line
    (wire, st1) <- goExpr st body
    Right st1 { stEnv = Map.insert name wire (stEnv st1) }

  SAdvice name hint line -> case gadget of
    -- The quarantine rule. Advice outside a gadget is not a style
    -- preference: it is the one construct that can silently make a circuit
    -- unsound, so writing it has to be a deliberate, visible act.
    Nothing -> Left $
      withHelp ("wrap it in a gadget block:  gadget my_gadget { advice "
                ++ name ++ " = ...; assert ...; }")
      $ withNotes
          [ "'advice' computes a value that no constraint pins down — the prover"
          , "chooses it freely, so it can only be used where its determinacy is"
          , "argued for explicitly. That is what a 'gadget' block marks."
          ]
      $ diagAt line ("'advice' may only appear inside a 'gadget' block")

    Just gadgetName -> do
      ensureFree st name line
      let (kindTag, argExpr) = case hint of
            HintInvOrZero e -> (KInvOrZero, e)
            HintInv e -> (KInv, e)
      (argWire, st1) <- goExpr st argExpr
      let wire = stNext st1
          info = HintInfo kindTag name gadgetName line
          node = Node wire (OHint info [argWire])
      Right st1 { stNext = wire + 1
                , stNodes = node : stNodes st1
                , stEnv = Map.insert name wire (stEnv st1) }

  SAssert lhs rhs line -> do
    (lw, st1) <- goExpr st lhs
    (rw, st2) <- goExpr st1 rhs
    let label = renderExpr lhs ++ " == " ++ renderExpr rhs
    Right st2 { stAsserts = Assertion lw rw label line : stAsserts st2 }

  SGadget name body line -> case gadget of
    Just outer -> Left $ diagAt line $
      "gadget '" ++ name ++ "' is nested inside gadget '" ++ outer
      ++ "'; phase 2 gadgets do not nest"
    -- Gadgets are markers, not scopes: bindings inside stay visible after
    -- the block. Phase 3 turns them into parameterised definitions, at which
    -- point they become real scopes.
    Nothing -> goStmts (Just name) st body

ensureFree :: St -> String -> Int -> Either Diagnostic ()
ensureFree st name line
  | Map.member name (stEnv st) = Left $ diagAt line ("'" ++ name ++ "' is already bound")
  | otherwise = Right ()

-- | Emit nodes for an expression, returning the wire holding its value.
goExpr :: St -> Expr -> Either Diagnostic (WireId, St)
goExpr st expr = case expr of
  ELit n _ -> Right (emit st (OConst n))
  EVar name line -> case Map.lookup name (stEnv st) of
    Just wire -> Right (wire, st)
    Nothing -> Left $ diagAt line ("'" ++ name ++ "' is not defined")
  EAdd a b _ -> binary st OAdd a b
  ESub a b _ -> binary st OSub a b
  EMul a b _ -> binary st OMul a b
  ENeg a _ -> do
    (w, st1) <- goExpr st a
    Right (emit st1 (ONeg w))
  where
    binary s make lhs rhs = do
      (lw, s1) <- goExpr s lhs
      (rw, s2) <- goExpr s1 rhs
      Right (emit s2 (make lw rw))

emit :: St -> Op -> (WireId, St)
emit st op =
  let wire = stNext st
  in (wire, st { stNext = wire + 1, stNodes = Node wire op : stNodes st })

-- | Advice that no assertion depends on cannot influence the circuit at all
-- (dead-code elimination would delete it), so it is always a mistake.
--
-- Note this is a *usefulness* check, not a soundness one — soundness is the
-- determinacy pass's job.
checkAdviceIsUsed :: Ir -> Either Diagnostic ()
checkAdviceIsUsed ir =
  case [ info | (wire, info) <- adviceWires ir, not (wire `Set.member` reachable) ] of
    [] -> Right ()
    (info : _) -> Left $
      withHelp "either constrain it with an assertion, or delete it"
      $ withNotes
          [ "a hint only tells the prover how to compute a value; with no"
          , "assertion depending on it, the value cannot affect anything"
          ]
      $ diagAt (hiLine info)
          ("advice '" ++ hiName info ++ "' is never used by any assertion")
  where
    nodeMap = Map.fromList [ (nWire n, nOp n) | n <- irNodes ir ]
    reachable = Set.unions [ cone (aLhs a) `Set.union` cone (aRhs a) | a <- irAssertions ir ]
    cone w = case Map.lookup w nodeMap of
      Nothing -> Set.singleton w
      Just op -> Set.insert w (Set.unions (map cone (opArgs op)))

-- | Render an expression back to source-ish text for assertion labels.
renderExpr :: Expr -> String
renderExpr e = case e of
  ELit n _ -> show n
  EVar name _ -> name
  EAdd a b _ -> "(" ++ renderExpr a ++ " + " ++ renderExpr b ++ ")"
  ESub a b _ -> "(" ++ renderExpr a ++ " - " ++ renderExpr b ++ ")"
  EMul a b _ -> "(" ++ renderExpr a ++ " * " ++ renderExpr b ++ ")"
  ENeg a _ -> "(-" ++ renderExpr a ++ ")"