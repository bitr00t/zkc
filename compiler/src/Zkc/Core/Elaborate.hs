-- | Elaboration: surface AST to Core IR, with scope and kind checking.
--
-- Phase 1 tracks the distinction that the whole language exists for:
--
--   * 'Determined' — the value is fixed by the constraints;
--   * 'Advice'     — computed by the witness generator, not yet constrained.
--
-- The checks here are deliberately the *weak* version. Phase 2 replaces the
-- \"advice must appear in some assertion\" heuristic with a real determinacy
-- pass. That gap is not hidden: @examples\/iszero_broken.zkc@ passes every
-- phase-1 check and still compiles to a forgeable circuit, which is exactly
-- the motivation for phase 2.
module Zkc.Core.Elaborate (elaborate, Kind(..)) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (intercalate)

import Zkc.Syntax.Ast
import Zkc.Core.Ir

-- | Whether a wire's value is pinned down by constraints.
data Kind = Determined | Advice
  deriving (Eq, Show)

data St = St
  { stNext :: WireId
  , stEnv :: Map.Map String (WireId, Kind)
  , stNodes :: [Node]          -- ^ reversed
  , stAsserts :: [Assertion]   -- ^ reversed
  }

-- | Elaborate a circuit, or fail with a source-located message.
elaborate :: String -> Circuit -> Either String Ir
elaborate fieldName circuit = do
  checkDuplicateParams (circParams circuit)
  let inputs = zipWith mkInput [1 ..] (circParams circuit)
      env0 = Map.fromList
        [ (pdName p, (iiWire i, Determined))
        | (p, i) <- zip (circParams circuit) inputs ]
      st0 = St { stNext = 1 + length inputs, stEnv = env0, stNodes = [], stAsserts = [] }
  st <- goStmts st0 (circBody circuit)
  let ir = Ir
        { irName = circName circuit
        , irField = fieldName
        , irInputs = inputs
        , irNodes = reverse (stNodes st)
        , irAssertions = reverse (stAsserts st)
        }
  checkAdviceConstrained ir
  Right ir
  where
    mkInput wire param = IrInput wire (pdName param) (pdVisibility param)

checkDuplicateParams :: [ParamDecl] -> Either String ()
checkDuplicateParams = go Set.empty
  where
    go _ [] = Right ()
    go seen (p:ps)
      | pdName p `Set.member` seen =
          Left $ "line " ++ show (pdLine p) ++ ": duplicate parameter '" ++ pdName p ++ "'"
      | otherwise = go (Set.insert (pdName p) seen) ps

goStmts :: St -> [Stmt] -> Either String St
goStmts = foldM'
  where
    foldM' st [] = Right st
    foldM' st (s:ss) = goStmt st s >>= \st' -> foldM' st' ss

goStmt :: St -> Stmt -> Either String St
goStmt st stmt = case stmt of
  SLet name body line -> do
    ensureFree st name line
    (wire, st1) <- goExpr st body
    -- A 'let' is the assign-and-constrain form, so the result is Determined
    -- whenever its operands are. (An advice value laundered through
    -- arithmetic stays advice — see 'combineKind'.)
    kind <- kindOfWire st1 wire line
    Right st1 { stEnv = Map.insert name (wire, kind) (stEnv st1) }

  SAdvice name hint line -> do
    ensureFree st name line
    (kindTag, argExpr) <- pure $ case hint of
      HintInvOrZero e -> (KInvOrZero, e)
      HintInv e -> (KInv, e)
    (argWire, st1) <- goExpr st argExpr
    let wire = stNext st1
        node = Node wire (OHint kindTag name [argWire])
        st2 = st1 { stNext = wire + 1
                  , stNodes = node : stNodes st1
                  , stEnv = Map.insert name (wire, Advice) (stEnv st1) }
    Right st2

  SAssert lhs rhs line -> do
    (lw, st1) <- goExpr st lhs
    (rw, st2) <- goExpr st1 rhs
    let label = renderExpr lhs ++ " == " ++ renderExpr rhs
    Right st2 { stAsserts = Assertion lw rw label line : stAsserts st2 }

ensureFree :: St -> String -> Int -> Either String ()
ensureFree st name line
  | Map.member name (stEnv st) =
      Left $ "line " ++ show line ++ ": '" ++ name ++ "' is already bound"
  | otherwise = Right ()

-- | Emit nodes for an expression, returning the wire holding its value.
goExpr :: St -> Expr -> Either String (WireId, St)
goExpr st expr = case expr of
  ELit n _ -> Right (emit st (OConst n))
  EVar name line -> case Map.lookup name (stEnv st) of
    Just (wire, _) -> Right (wire, st)
    Nothing -> Left $ "line " ++ show line ++ ": '" ++ name ++ "' is not defined"
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

-- | A wire is Advice if it (transitively) depends on a hint.
kindOfWire :: St -> WireId -> Int -> Either String Kind
kindOfWire st wire _ = Right (go wire)
  where
    nodes = Map.fromList [ (nWire n, nOp n) | n <- stNodes st ]
    go w = case Map.lookup w nodes of
      Nothing -> Determined                       -- input or constant-one
      Just op | isHint op -> Advice
              | otherwise -> combineKind (map go (opArgs op))

combineKind :: [Kind] -> Kind
combineKind ks = if Advice `elem` ks then Advice else Determined

-- | Phase-1 approximation of the determinacy pass: every advice wire must at
-- least be *mentioned* by some assertion.
--
-- This catches the crudest mistake (a hint nobody ever constrains) and
-- nothing more. It cannot tell whether the assertions determine the value
-- uniquely — that needs phase 2.
checkAdviceConstrained :: Ir -> Either String ()
checkAdviceConstrained ir =
  case filter (not . (`Set.member` reachableFromAsserts)) adviceWires of
    [] -> Right ()
    orphans -> Left $
      "unconstrained advice: wire(s) " ++ intercalate ", " (map show orphans)
      ++ " are computed by a hint but no assertion mentions them.\n"
      ++ "  A hint only tells the prover how to compute a value; without an\n"
      ++ "  assertion the prover may substitute any other value instead."
  where
    nodeMap = Map.fromList [ (nWire n, nOp n) | n <- irNodes ir ]
    adviceWires = [ nWire n | n <- irNodes ir, isHint (nOp n) ]
    reachableFromAsserts =
      Set.unions [ cone (aLhs a) `Set.union` cone (aRhs a) | a <- irAssertions ir ]
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