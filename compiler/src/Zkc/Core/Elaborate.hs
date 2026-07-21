-- | Elaboration: surface 'Program' to Core IR, with scopes, quarantine checks
-- and gadget inlining.
--
-- Phase 2 kept the rule that made circuit code sound by construction:
--
--   * @let@ computes /and/ constrains, so ordinary code cannot create an
--     unconstrained value at all;
--   * @advice@ computes /without/ constraining, and is legal only inside a
--     gadget — an explicit, greppable marker that something subtle happens.
--
-- Phase 3 turns gadgets into parameterised definitions with real scopes.
-- Elaboration now does two things at once:
--
--   1. it inlines every instantiation into one flat 'Ir' — all the backend
--      ever sees, unchanged from phase 2;
--   2. it records, for the circuit and for each gadget, a 'Body' skeleton
--      that keeps instantiations symbolic, so the determinacy pass can reason
--      about a gadget once and reuse the result at each call site rather than
--      re-expanding it.
--
-- Two scoping rules the phase-2 marker gadgets lacked: a gadget body is its
-- own scope (its bindings do not leak into the circuit, and vice versa,
-- except through parameters and results), and each instantiation gets fresh
-- wires, so calling the same gadget twice cannot accidentally share state.
module Zkc.Core.Elaborate
  ( elaborate
  , Elaborated(..)
  , resultKinds
  , ResultKind(..)
  ) where

import Data.List (foldl', nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Zkc.Diagnostics
import Zkc.Syntax.Ast
import Zkc.Core.Ir

-- | The whole elaborated program: the flat IR for the backend, plus the
-- skeletons the determinacy pass consumes.
data Elaborated = Elaborated
  { elabIr :: Ir
  , elabGadgetBodies :: [(GadgetDef, Body)]  -- ^ in dependency order (callees first)
  , elabCircuitBody :: Body
  } deriving (Eq, Show)

-- | Whether a gadget result is a bare atom the body only /constrains/, or a
-- value the body /computes/ (with @let@ or @advice@). It decides which call
-- form is legal: an atom result binds to an existing output, a computed one
-- can be bound freshly.
data ResultKind = ResultAtom | ResultComputed
  deriving (Eq, Show)

-- | Classify each of a gadget's results by scanning its body for a binding.
resultKinds :: GadgetDef -> Map.Map String ResultKind
resultKinds def = Map.fromList
  [ (r, if r `Set.member` bound then ResultComputed else ResultAtom)
  | r <- gdResults def ]
  where
    bound = Set.fromList (concatMap boundNames (gdBody def))
    boundNames s = case s of
      SLet n _ _ -> [n]
      SAdvice n _ _ -> [n]
      SInstance bind _ _ _ -> bindNames bind
      SAssert{} -> []

bindNames :: InstanceBind -> [String]
bindNames (BindExisting ns) = ns
bindNames (BindFresh ns) = ns

-- | Elaborate a program, or fail with a source-located diagnostic.
elaborate :: String -> Program -> Either Diagnostic Elaborated
elaborate fieldName program = do
  let gadgets = progGadgets program
      gadgetMap = Map.fromList [ (gdName g, g) | g <- gadgets ]
  checkNoDuplicateGadgets gadgets
  -- Every gadget definition is a small circuit in its own right; validate and
  -- skeletonise each, in an order where a gadget's callees come first.
  ordered <- orderGadgets gadgets
  bodies <- mapM (\g -> (,) g <$> gadgetBody gadgetMap g) ordered
  -- The circuit, fully inlined into flat IR plus its own skeleton.
  (ir, circuitBody) <- circuit fieldName gadgetMap (progCircuit program)
  Right (Elaborated ir bodies circuitBody)

checkNoDuplicateGadgets :: [GadgetDef] -> Either Diagnostic ()
checkNoDuplicateGadgets = go Set.empty
  where
    go _ [] = Right ()
    go seen (g:gs)
      | gdName g `Set.member` seen =
          Left $ diagAt (gdLine g) ("duplicate gadget '" ++ gdName g ++ "'")
      | otherwise = go (Set.insert (gdName g) seen) gs

-- | Topologically order gadgets so a definition's callees precede it. Rejects
-- unknown callees and cycles (a circuit is finite: gadgets cannot recurse).
orderGadgets :: [GadgetDef] -> Either Diagnostic [GadgetDef]
orderGadgets gadgets = go [] Set.empty gadgets
  where
    byName = Map.fromList [ (gdName g, g) | g <- gadgets ]
    callees g = nub [ n | SInstance _ n _ _ <- gdBody g ]

    go done _ [] = Right (reverse done)
    go done onStack pending = case pickReady done pending of
      Just g -> go (g : done) onStack (filter ((/= gdName g) . gdName) pending)
      Nothing -> case pending of
        (g:_) -> reportProblem g
        []    -> Right (reverse done)
      where
        doneNames = Set.fromList (map gdName done)
        pickReady _ [] = Nothing
        pickReady _ (g:gs)
          | all resolved (callees g) = Just g
          | otherwise = pickReady done gs
          where resolved c = c `Set.member` doneNames
                _ = gs

    reportProblem g =
      case [ c | c <- callees g, not (c `Map.member` byName) ] of
        (missing:_) -> Left $ diagAt (gdLine g) $
          "gadget '" ++ gdName g ++ "' instantiates unknown gadget '" ++ missing ++ "'"
        [] -> Left $ diagAt (gdLine g) $
          "gadget '" ++ gdName g ++ "' is part of a cycle; gadgets cannot recurse"

-- Shared elaboration state -----------------------------------------------

data St = St
  { stNext :: WireId
  , stEnv :: Map.Map String WireId
  , stFlatNodes :: [Node]        -- ^ reversed; ALL nodes, incl. inlined bodies
  , stFlatAsserts :: [Assertion] -- ^ reversed; ALL assertions
  , stOwnNodes :: [Node]         -- ^ reversed; nodes written at the current top level
  , stOwnAsserts :: [Assertion]  -- ^ reversed; assertions at the current top level
  , stInstances :: [InstanceSite] -- ^ reversed; top-level instances
  }

-- Circuit elaboration ----------------------------------------------------

circuit :: String -> Map.Map String GadgetDef -> Circuit -> Either Diagnostic (Ir, Body)
circuit fieldName gadgetMap circ = do
  checkDuplicateParams (circParams circ)
  let inputs = zipWith mkInput [1 ..] (circParams circ)
      env0 = Map.fromList [ (pdName p, iiWire i) | (p, i) <- zip (circParams circ) inputs ]
      st0 = St { stNext = 1 + length inputs, stEnv = env0
               , stFlatNodes = [], stFlatAsserts = []
               , stOwnNodes = [], stOwnAsserts = [], stInstances = [] }
  st <- goStmts gadgetMap Nothing st0 (circBody circ)
  -- Wires produced inside an instance are not the circuit's own; the circuit's
  -- atoms are its inputs plus the result wires the instances handed back.
  let instanceResultWires = concatMap isResults (reverse (stInstances st))
      freshResultAtoms =
        [ IrInput w (nameFor st w) Private 0
        | w <- instanceResultWires
        , w `notElem` map iiWire inputs ]
      ir = Ir
        { irName = circName circ
        , irField = fieldName
        , irInputs = inputs
        , irNodes = reverse (stFlatNodes st)
        , irAssertions = reverse (stFlatAsserts st)
        }
      body = Body
        { bodyParams = [ iiWire i | i <- inputs, iiVisibility i /= Output ]
        , bodyResultTargets = [ iiWire i | i <- inputs, iiVisibility i == Output ]
        , bodyRequires = []
        , bodyAtoms = inputs ++ freshResultAtoms
        , bodyNodes = reverse (stOwnNodes st)
        , bodyAsserts = reverse (stOwnAsserts st)
        , bodyInstances = reverse (stInstances st)
        }
  checkAdviceIsUsed ir
  Right (ir, body)
  where
    mkInput wire param = IrInput wire (pdName param) (pdVisibility param) (pdLine param)
    nameFor st w = maybe ("wire" ++ show w) id
      (lookup w [ (v, k) | (k, v) <- Map.toList (stEnv st) ])

checkDuplicateParams :: [ParamDecl] -> Either Diagnostic ()
checkDuplicateParams = go Set.empty
  where
    go _ [] = Right ()
    go seen (p:ps)
      | pdName p `Set.member` seen =
          Left $ diagAt (pdLine p) ("duplicate parameter '" ++ pdName p ++ "'")
      | otherwise = go (Set.insert (pdName p) seen) ps

-- | Statement elaboration. The first argument is the enclosing gadget name, if
-- any — 'Nothing' at circuit level, which is what makes @advice@ there an
-- error.
goStmts :: Map.Map String GadgetDef -> Maybe String -> St -> [Stmt] -> Either Diagnostic St
goStmts gadgetMap enclosing = go
  where
    go st [] = Right st
    go st (s:ss) = goStmt gadgetMap enclosing st s >>= \st' -> go st' ss

goStmt :: Map.Map String GadgetDef -> Maybe String -> St -> Stmt -> Either Diagnostic St
goStmt gadgetMap enclosing st stmt = case stmt of
  SLet name body line -> do
    ensureFree st name line
    (wire, st1) <- goExpr st body
    Right st1 { stEnv = Map.insert name wire (stEnv st1) }

  SAdvice name hint line -> case enclosing of
    Nothing -> Left $
      withHelp ("wrap it in a gadget definition:  gadget my_gadget(..) -> (..) { advice "
                ++ name ++ " = ...; assert ...; }")
      $ withNotes
          [ "'advice' computes a value that no constraint pins down — the prover"
          , "chooses it freely, so it is legal only where its determinacy is"
          , "argued for explicitly. That is what a 'gadget' definition marks."
          ]
      $ diagAt line "'advice' may only appear inside a 'gadget' definition"

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
                , stFlatNodes = node : stFlatNodes st1
                , stOwnNodes = node : stOwnNodes st1
                , stEnv = Map.insert name wire (stEnv st1) }

  SAssert lhs rhs line -> do
    (lw, st1) <- goExpr st lhs
    (rw, st2) <- goExpr st1 rhs
    let label = renderExpr lhs ++ " == " ++ renderExpr rhs
        a = Assertion lw rw label line
    Right st2 { stFlatAsserts = a : stFlatAsserts st2
              , stOwnAsserts = a : stOwnAsserts st2 }

  SInstance bind gadgetName args line ->
    instantiate gadgetMap enclosing st bind gadgetName args line

-- | Inline one instantiation into the flat IR and record its site.
instantiate :: Map.Map String GadgetDef -> Maybe String -> St
            -> InstanceBind -> String -> [Expr] -> Int
            -> Either Diagnostic St
instantiate gadgetMap enclosing st bind gadgetName args line = do
  def <- case Map.lookup gadgetName gadgetMap of
    Just d -> Right d
    Nothing -> Left $ diagAt line ("unknown gadget '" ++ gadgetName ++ "'")
  -- Arity checks, with source-friendly messages.
  let names = bindNames bind
  arityCheck line "argument" gadgetName (length (gdParams def)) (length args)
  arityCheck line "result" gadgetName (length (gdResults def)) (length names)
  -- Evaluate the arguments in the caller's scope.
  (argWires, st1) <- goArgs st args
  let kinds = resultKinds def
  -- Resolve result wires and a pre-binding for the inline scope.
  (resultWires, preResults, st2) <- resolveResults st1 def bind names kinds line
  -- Inline the body under a fresh scope: params and (pre-)results substituted,
  -- everything else fresh.
  let inlineEnv = Map.fromList (zip (gdParams def) argWires ++ preResults)
      st3 = st2 { stEnv = inlineEnv }
  st4 <- goStmts gadgetMap (Just gadgetName) st3 (gdBody def)
  -- Read back computed results the body bound, in result order.
  finalResults <- mapM (readResult st4 gadgetName line kinds) (zip (gdResults def) resultWires)
  let site = InstanceSite gadgetName argWires finalResults line
      -- Restore the caller's scope, then bind the caller-visible result names.
      restored = st4 { stEnv = stEnv st1 }
      callerEnv = case bind of
        BindExisting _ -> stEnv restored   -- outputs already in scope
        BindFresh ns -> foldl' (\e (n, w) -> Map.insert n w e) (stEnv restored) (zip ns finalResults)
  Right restored
    { stEnv = callerEnv
    , stInstances = site : stInstances restored
    }

-- | A result wire is either an existing output (bind-existing) or freshly
-- introduced by the body (bind-fresh). Fresh atom-results are impossible: the
-- body never gives them a defining node, so there would be nothing to bind.
resolveResults :: St -> GadgetDef -> InstanceBind -> [String]
               -> Map.Map String ResultKind -> Int
               -> Either Diagnostic ([WireId], [(String, WireId)], St)
resolveResults st def bind names kinds line = case bind of
  BindExisting _ -> do
    wires <- mapM lookupExisting names
    Right (wires, zip (gdResults def) wires, st)
  BindFresh _ -> do
    mapM_ ensureFreshName names
    mapM_ ensureComputed (gdResults def)
    -- Fresh results are read back from the body after inlining; leave the
    -- inline scope to bind them.
    Right (replicate (length names) (-1), [], st)
  where
    lookupExisting name = case Map.lookup name (stEnv st) of
      Just w -> Right w
      Nothing -> Left $ diagAt line $
        "'" ++ name ++ "' is not a declared output; a plain '(" ++ name
        ++ ") = ...' binds an existing output — use 'let (" ++ name
        ++ ") = ...' to introduce a new wire"
    ensureFreshName name
      | Map.member name (stEnv st) = Left $ diagAt line ("'" ++ name ++ "' is already bound")
      | otherwise = Right ()
    ensureComputed r = case Map.lookup r kinds of
      Just ResultComputed -> Right ()
      _ -> Left $
        withHelp ("bind it to a declared output instead:  (" ++ r ++ ") = "
                  ++ gdName def ++ "(...);")
        $ diagAt line $
          "result '" ++ r ++ "' of gadget '" ++ gdName def
          ++ "' is not computed by its body, so it cannot be bound with 'let'"

-- | After inlining, look up where each result landed.
readResult :: St -> String -> Int -> Map.Map String ResultKind -> (String, WireId)
           -> Either Diagnostic WireId
readResult st gadgetName line kinds (resultName, preWire)
  | preWire /= (-1) = Right preWire   -- bind-existing: already resolved
  | otherwise = case Map.lookup resultName (stEnv st) of
      Just w -> Right w
      Nothing -> Left $ diagAt line $
        "gadget '" ++ gadgetName ++ "' never binds its result '" ++ resultName ++ "'"
  where _ = kinds

arityCheck :: Int -> String -> String -> Int -> Int -> Either Diagnostic ()
arityCheck line what gadgetName expected got
  | expected == got = Right ()
  | otherwise = Left $ diagAt line $
      "gadget '" ++ gadgetName ++ "' expects " ++ show expected ++ " " ++ what
      ++ (if expected == 1 then "" else "s") ++ ", got " ++ show got

goArgs :: St -> [Expr] -> Either Diagnostic ([WireId], St)
goArgs st [] = Right ([], st)
goArgs st (e:es) = do
  (w, st1) <- goExpr st e
  (ws, st2) <- goArgs st1 es
  Right (w : ws, st2)

ensureFree :: St -> String -> Int -> Either Diagnostic ()
ensureFree st name line
  | Map.member name (stEnv st) = Left $ diagAt line ("'" ++ name ++ "' is already bound")
  | otherwise = Right ()

-- | Emit nodes for an expression (to both the flat IR and the current scope's
-- own list), returning the wire holding its value.
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
      node = Node wire op
  in (wire, st { stNext = wire + 1
               , stFlatNodes = node : stFlatNodes st
               , stOwnNodes = node : stOwnNodes st })

-- Gadget-body skeletons --------------------------------------------------

-- | Build a gadget's 'Body' skeleton in local numbering (wire 0 is one, then
-- params, then atom-results, then internals). Instantiations inside the body
-- are kept symbolic. This is what the determinacy pass proves, once.
gadgetBody :: Map.Map String GadgetDef -> GadgetDef -> Either Diagnostic Body
gadgetBody gadgetMap def = do
  checkDuplicateNames def
  let kinds = resultKinds def
      params = gdParams def
      atomResults = [ r | r <- gdResults def, Map.lookup r kinds == Just ResultAtom ]
      paramWires = [1 .. length params]
      atomWires = [ length params + 1 .. length params + length atomResults ]
      paramInputs = [ IrInput w n Private 0 | (w, n) <- zip paramWires params ]
      atomInputs = [ IrInput w n Output 0 | (w, n) <- zip atomWires atomResults ]
      env0 = Map.fromList (zip params paramWires ++ zip atomResults atomWires)
      st0 = St { stNext = 1 + length params + length atomResults, stEnv = env0
               , stFlatNodes = [], stFlatAsserts = []
               , stOwnNodes = [], stOwnAsserts = [], stInstances = [] }
  st <- goSkelStmts gadgetMap def st0 (gdBody def)
  resultWires <- mapM (resultWire st) (gdResults def)
  requireWires <- mapM (requireWire params paramWires) (gdRequires def)
  let instanceResultWires = concatMap isResults (reverse (stInstances st))
      instanceAtoms =
        [ IrInput w ("_r" ++ show w) Private 0
        | w <- instanceResultWires, w `notElem` (paramWires ++ atomWires) ]
  Right Body
    { bodyParams = paramWires
    , bodyResultTargets = resultWires
    , bodyRequires = requireWires
    , bodyAtoms = paramInputs ++ atomInputs ++ instanceAtoms
    , bodyNodes = reverse (stOwnNodes st)
    , bodyAsserts = reverse (stOwnAsserts st)
    , bodyInstances = reverse (stInstances st)
    }
  where
    resultWire st r = case Map.lookup r (stEnv st) of
      Just w -> Right w
      Nothing -> Left $ diagAt (gdLine def) $
        "gadget '" ++ gdName def ++ "' declares result '" ++ r
        ++ "' but its body never constrains it"
    requireWire params paramWires (Require name l) =
      case lookup name (zip params paramWires) of
        Just w -> Right w
        Nothing -> Left $ diagAt l $
          "'require " ++ name ++ " != 0' names '" ++ name
          ++ "', which is not a parameter of gadget '" ++ gdName def ++ "'"

checkDuplicateNames :: GadgetDef -> Either Diagnostic ()
checkDuplicateNames def =
  let ps = gdParams def
  in case firstDup ps of
       Just d -> Left $ diagAt (gdLine def) ("duplicate parameter '" ++ d ++ "' in gadget '" ++ gdName def ++ "'")
       Nothing -> Right ()
  where
    firstDup = go Set.empty
    go _ [] = Nothing
    go seen (x:xs) | x `Set.member` seen = Just x
                   | otherwise = go (Set.insert x seen) xs

-- | Statement elaboration for a gadget skeleton: like 'goStmt' but keeps
-- nested instances symbolic rather than inlining them.
goSkelStmts :: Map.Map String GadgetDef -> GadgetDef -> St -> [Stmt] -> Either Diagnostic St
goSkelStmts gadgetMap def = go
  where
    go st [] = Right st
    go st (s:ss) = goSkelStmt gadgetMap def st s >>= \st' -> go st' ss

goSkelStmt :: Map.Map String GadgetDef -> GadgetDef -> St -> Stmt -> Either Diagnostic St
goSkelStmt gadgetMap def st stmt = case stmt of
  SLet name body line -> do
    ensureFree st name line
    (wire, st1) <- goExpr st body
    Right st1 { stEnv = Map.insert name wire (stEnv st1) }

  SAdvice name hint line -> do
    ensureFree st name line
    let (kindTag, argExpr) = case hint of
          HintInvOrZero e -> (KInvOrZero, e)
          HintInv e -> (KInv, e)
    (argWire, st1) <- goExpr st argExpr
    let wire = stNext st1
        info = HintInfo kindTag name (gdName def) line
        node = Node wire (OHint info [argWire])
    Right st1 { stNext = wire + 1
              , stOwnNodes = node : stOwnNodes st1
              , stEnv = Map.insert name wire (stEnv st1) }

  SAssert lhs rhs line -> do
    (lw, st1) <- goExpr st lhs
    (rw, st2) <- goExpr st1 rhs
    let label = renderExpr lhs ++ " == " ++ renderExpr rhs
    Right st2 { stOwnAsserts = Assertion lw rw label line : stOwnAsserts st2 }

  SInstance bind calleeName args line -> do
    callee <- case Map.lookup calleeName gadgetMap of
      Just d -> Right d
      Nothing -> Left $ diagAt line ("unknown gadget '" ++ calleeName ++ "'")
    let names = bindNames bind
    arityCheck line "argument" calleeName (length (gdParams callee)) (length args)
    arityCheck line "result" calleeName (length (gdResults callee)) (length names)
    (argWires, st1) <- goArgs st args
    -- Allocate a fresh atom wire per result; the summary treats it as an atom
    -- the callee determines.
    let base = stNext st1
        resultWires = [ base .. base + length names - 1 ]
        st2 = st1 { stNext = base + length names }
        env' = case bind of
          BindExisting ns -> foldl' bindExisting (stEnv st2) ns
          BindFresh ns -> foldl' (\e (n, w) -> Map.insert n w e) (stEnv st2) (zip ns resultWires)
        bindExisting e n = maybe e (\w -> Map.insert n w e) (Map.lookup n (stEnv st2))
        -- For bind-existing the result wires are the already-bound names.
        finalResults = case bind of
          BindExisting ns -> [ maybe w id (Map.lookup n (stEnv st2)) | (n, w) <- zip ns resultWires ]
          BindFresh _ -> resultWires
        site = InstanceSite calleeName argWires finalResults line
    Right st2 { stEnv = env', stInstances = site : stInstances st2 }

-- Shared checks ----------------------------------------------------------

-- | Advice that no assertion depends on cannot influence the circuit at all
-- (dead-code elimination would delete it), so it is always a mistake.
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

renderExpr :: Expr -> String
renderExpr e = case e of
  ELit n _ -> show n
  EVar name _ -> name
  EAdd a b _ -> "(" ++ renderExpr a ++ " + " ++ renderExpr b ++ ")"
  ESub a b _ -> "(" ++ renderExpr a ++ " - " ++ renderExpr b ++ ")"
  EMul a b _ -> "(" ++ renderExpr a ++ " * " ++ renderExpr b ++ ")"
  ENeg a _ -> "(-" ++ renderExpr a ++ ")"