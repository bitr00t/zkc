-- | The determinacy pass — the reason this compiler exists.
--
-- == What must be proved
--
-- A circuit is /sound/ when its declared outputs are a function of its
-- inputs: for any fixed inputs, at most one assignment to the outputs
-- satisfies the constraints. If two different outputs both satisfy, the
-- prover picks whichever it likes and proves a falsehood — that is exactly
-- the under-constraining bug, stated precisely.
--
-- Advice wires need not be determined. In @IsZero@, when @x = 0@ the helper
-- @inv@ genuinely may be anything, and the circuit is still sound because
-- @out@ is pinned regardless. A checker that demanded every advice wire be
-- determined would reject correct code.
--
-- == How it is proved
--
-- Each assertion becomes a polynomial equation @P = 0@ over the circuit's
-- /atoms/ (declared wires and advice wires). Then two rules, applied to
-- exhaustion: __linear propagation__ (an equation @c*u + r = 0@ with @u@ the
-- only unknown, @c@ and @r@ computable from determined atoms and @c@ known
-- nonzero, pins @u@) and __case splitting__ (branch a determined atom on
-- @= 0@ vs @/= 0@; a branch whose equations reduce to a nonzero constant is
-- infeasible and discharged).
--
-- == Phase 3: compositional proofs
--
-- A gadget is proved __once__, as its own little determinacy problem (its
-- parameters determined, its results the targets), yielding a 'Summary'. At a
-- call site the summary is /applied/ — the results are marked determined and
-- any nonzero guarantee is recorded — without re-expanding the body into the
-- caller's polynomial system. That is what keeps a 32-deep Merkle path inside
-- the monomial budget: the expensive expansion happens per definition, not
-- per instantiation.
--
-- == Limits, stated plainly
--
-- Splitting is depth-bounded and the analysis is incomplete: a failure means
-- \"not proved\", not \"proved unsound\". Since the pass rejects on failure,
-- incompleteness costs expressiveness, never safety. Polynomial expansion is
-- also exponential in the worst case, so there is a hard cap on size — now
-- applied per gadget rather than to the whole inlined circuit. Both limits
-- are eased further by the SMT escalation planned for the rest of phase 3.
module Zkc.Analysis.Determinacy
  ( checkDeterminacy
  , checkProgram
  , Assumption(..)
  , Report(..)
  , Failure(..)
  , maxSplitDepth
  ) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Zkc.Analysis.Poly
import Zkc.Core.Ir
import Zkc.Syntax.Ast (Visibility(..), GadgetDef(..))

-- | How deep the case-split search may go.
maxSplitDepth :: Int
maxSplitDepth = 3

-- | Guard against polynomial blow-up. Now a per-gadget budget: composition
-- means the whole circuit is never expanded at once.
maxMonomials :: Int
maxMonomials = 4096

data Assumption
  = AssumeZero WireId
  | AssumeNonZero WireId
  deriving (Eq, Show)

data Report = Report
  { repTargets :: [WireId]
  , repAssumptions :: [[Assumption]]
  } deriving (Eq, Show)

data Failure = Failure
  { failTarget :: WireId
  , failAssumptions :: [Assumption]
  , failFreeAdvice :: [WireId]
  , failNote :: Maybe String
  } deriving (Eq, Show)

data Branch = Branch
  { brDetermined :: Set.Set WireId
  , brNonzero :: Set.Set WireId
  , brZeroed :: Set.Set WireId       -- ^ atoms assumed zero on this path
  , brEquations :: [Poly]
  , brAssumptions :: [Assumption]
  , brAssumed :: Set.Set WireId
  }

-- Monolithic entry point (phase 2, unchanged behaviour) -------------------

-- | Prove that every declared output of a flat IR is determined by the
-- inputs. This still runs on the fully-inlined IR and is what the test suite
-- and the optimiser-equivalence check exercise.
checkDeterminacy :: Integer -> Ir -> Either Failure Report
checkDeterminacy modulus ir = do
  wirePolys <- buildPolynomials modulus (map iiWire (irInputs ir)) (irNodes ir)
  let equations =
        [ sub modulus (wirePolys Map.! aLhs a) (wirePolys Map.! aRhs a)
        | a <- irAssertions ir ]
      determined = Set.fromList
        [ iiWire i | i <- irInputs ir, iiVisibility i /= Output ]
      targets = [ iiWire i | i <- irInputs ir, iiVisibility i == Output ]
  case targets of
    [] -> Right (Report [] [])
    _ -> do
      branches <- searchWith modulus (map fst (adviceWires ir)) wirePolys
                    determined Set.empty targets maxSplitDepth (root determined equations)
      Right (Report targets branches)
  where
    root determined equations = Branch
      { brDetermined = determined
      , brNonzero = Set.empty
      , brZeroed = Set.empty
      , brEquations = equations
      , brAssumptions = []
      , brAssumed = Set.empty
      }

-- Compositional entry point (phase 3) ------------------------------------

-- | A gadget's proof, cached for reuse at every call site.
data Summary = Summary
  { sumParamWires :: [WireId]     -- ^ the gadget's params, in order (local numbering)
  , sumResultWires :: [WireId]    -- ^ the gadget's results, in order (local numbering)
  , sumBranches :: [[Assumption]] -- ^ case splits, over local param\/result wires
  , sumRequired :: [Int]          -- ^ param indices with a @require ... != 0@
  , sumNonzero :: [Int]           -- ^ param indices guaranteed nonzero by the body
  }

-- | Prove every gadget (in the given callees-first order) and then the
-- circuit, applying summaries at instantiation sites.
checkProgram :: Integer -> [(GadgetDef, Body)] -> Body -> Either Failure Report
checkProgram modulus gadgetBodies circuitBody = do
  summaries <- foldl' proveNext (Right Map.empty) gadgetBodies
  (branches, _) <- proveBody modulus summaries circuitBody
  Right (Report (bodyResultTargets circuitBody) branches)
  where
    proveNext acc (def, body) = do
      done <- acc
      summary <- summariseGadget modulus done def body
      Right (Map.insert (gdName def) summary done)

-- | Prove one gadget definition and package the result as a 'Summary'.
summariseGadget :: Integer -> Map.Map String Summary -> GadgetDef -> Body
                -> Either Failure Summary
summariseGadget modulus summaries def body = do
  (branches, _) <- proveBody modulus summaries body
  guaranteed <- guaranteedNonzeroParams modulus summaries body
  Right Summary
    { sumParamWires = bodyParams body
    , sumResultWires = bodyResultTargets body
    , sumBranches = branches
    , sumRequired = [ i | (i, w) <- zip [0 ..] (bodyParams body), w `elem` bodyRequires body ]
    , sumNonzero = guaranteed
    }

-- | The heart of composition: prove a body's result targets determined,
-- applying summaries for the instances it contains rather than expanding them.
-- Returns the branches the proof rested on and the wires it can now treat as
-- nonzero (for the caller's benefit).
proveBody :: Integer -> Map.Map String Summary -> Body
          -> Either Failure ([[Assumption]], Set.Set WireId)
proveBody modulus summaries body = do
  wirePolys <- buildPolynomials modulus (Set.toList atomWires) (bodyNodes body)
  -- Fold the instances in order, threading determined\/nonzero sets and
  -- collecting the (remapped) branches each contributed.
  (determined1, nonzero1, instanceBranches) <-
    foldl' (applyInstance summaries) (Right (determined0, nonzero0, [])) (bodyInstances body)
  let equations =
        [ sub modulus (wirePolys Map.! aLhs a) (wirePolys Map.! aRhs a)
        | a <- bodyAsserts body ]
      remaining = [ t | t <- bodyResultTargets body, not (targetKnown wirePolys determined1 Set.empty t) ]
      advice = [ nWire n | n <- bodyNodes body, isHint (nOp n) ]
  ownBranches <-
    if null remaining
      then Right [[]]
      else searchWith modulus advice wirePolys determined1 nonzero1 (bodyResultTargets body)
             maxSplitDepth (rootBranch determined1 nonzero1 equations)
  Right (combine instanceBranches ownBranches, nonzero1)
  where
    atomWires = Set.fromList
      ([ iiWire i | i <- bodyAtoms body ] ++ bodyParams body ++ bodyResultTargets body)
    determined0 = Set.fromList (bodyParams body)
    nonzero0 = Set.fromList (bodyRequires body)
    rootBranch determined nonzero equations = Branch
      { brDetermined = determined
      , brNonzero = nonzero
      , brZeroed = Set.empty
      , brEquations = equations
      , brAssumptions = []
      , brAssumed = Set.empty
      }

-- | Apply one instance's summary, extending the determined and nonzero sets
-- and remapping its branches into the caller's wires.
applyInstance :: Map.Map String Summary
              -> Either Failure (Set.Set WireId, Set.Set WireId, [[Assumption]])
              -> InstanceSite
              -> Either Failure (Set.Set WireId, Set.Set WireId, [[Assumption]])
applyInstance summaries acc site = do
  (determined, nonzero, branches) <- acc
  summary <- case Map.lookup (isGadget site) summaries of
    Just s -> Right s
    Nothing -> Left Failure
      { failTarget = -1, failAssumptions = [], failFreeAdvice = []
      , failNote = Just ("internal: no summary for gadget '" ++ isGadget site ++ "'") }
  -- Discharge each precondition: the corresponding argument must be known
  -- nonzero in the caller's context.
  let args = isArgs site
      undischarged =
        [ i | i <- sumRequired summary
            , not ((args !! i) `Set.member` nonzero) ]
  case undischarged of
    (i:_) -> Left Failure
      { failTarget = args !! i
      , failAssumptions = []
      , failFreeAdvice = []
      , failNote = Just $
          "gadget '" ++ isGadget site ++ "' requires its argument to be nonzero here, "
          ++ "but the caller cannot show it is. Establish it (e.g. with a gadget that "
          ++ "guarantees it) before this call." }
    [] -> do
      let remap = Map.fromList $
            zip (sumParamWires summary) (isArgs site)
            ++ zip (sumResultWires summary) (isResults site)
          remapped = map (remapAssumptions remap) (sumBranches summary)
          determined' = foldr Set.insert determined (isResults site)
          nonzero' = foldr Set.insert nonzero
            [ isArgs site !! i | i <- sumNonzero summary ]
      Right (determined', nonzero', combine branches remapped)

-- | Rename the wires an assumption speaks about, dropping any that do not map
-- to a caller wire (a purely internal split the caller need not hear about).
remapAssumptions :: Map.Map WireId WireId -> [Assumption] -> [Assumption]
remapAssumptions remap = concatMap step
  where
    step (AssumeZero w) = [ AssumeZero w' | Just w' <- [Map.lookup w remap] ]
    step (AssumeNonZero w) = [ AssumeNonZero w' | Just w' <- [Map.lookup w remap] ]

-- | Combine two lists of case-split paths. Each gadget's internal split is
-- discharged inside its own summary, so at a call site its branches are just
-- /reported/, not re-multiplied against the caller's: independent per-gadget
-- analyses concatenate (2N paths for N instances), they do not explode into a
-- 2^N cross-product. A single empty path means \"no split here\" and drops out.
combine :: [[Assumption]] -> [[Assumption]] -> [[Assumption]]
combine [] bs = bs
combine as [] = as
combine [[]] bs = bs
combine as [[]] = as
combine as bs = as ++ bs

-- | Which parameters does the body force nonzero? A param @p@ is guaranteed
-- nonzero when assuming @p = 0@ makes the body infeasible — its equations
-- collapse to a nonzero constant. This is what lets a gadget export a fact its
-- callers can use to discharge their own preconditions.
guaranteedNonzeroParams :: Integer -> Map.Map String Summary -> Body -> Either Failure [Int]
guaranteedNonzeroParams modulus summaries body = do
  wirePolys <- buildPolynomials modulus (Set.toList atomWires) (bodyNodes body)
  let equations =
        [ sub modulus (wirePolys Map.! aLhs a) (wirePolys Map.! aRhs a)
        | a <- bodyAsserts body ]
  Right [ i | (i, p) <- zip [0 ..] (bodyParams body)
            , infeasibleWhenZero p equations ]
  where
    atomWires = Set.fromList
      ([ iiWire i | i <- bodyAtoms body ] ++ bodyParams body ++ bodyResultTargets body)
    _ = summaries
    infeasibleWhenZero p equations =
      let zeroed = map (substituteZero p) equations
          branch = saturate modulus Branch
            { brDetermined = Set.fromList (bodyParams body)
            , brNonzero = Set.empty, brZeroed = Set.singleton p
            , brEquations = zeroed, brAssumptions = [], brAssumed = Set.empty }
      in any isNonzeroConst (brEquations branch)
    isNonzeroConst poly = case asConstant poly of
      Just v -> v /= 0
      Nothing -> False

-- Shared polynomial construction -----------------------------------------

-- | Expand every wire into a polynomial over the atoms. Atoms are the given
-- atom wires (inputs, results, instance results) and advice wires; arithmetic
-- nodes are expanded away.
buildPolynomials :: Integer -> [WireId] -> [Node] -> Either Failure (Map.Map WireId Poly)
buildPolynomials modulus atomWires nodes = go initial nodes
  where
    initial = Map.fromList $
      (constOneWire, constant modulus 1)
      : [ (w, var modulus w) | w <- atomWires ]

    go acc [] = Right acc
    go acc (node : rest) = do
      let arg index = Map.findWithDefault (var modulus (opArgs (nOp node) !! index))
                        (opArgs (nOp node) !! index) acc
      poly <- case nOp node of
        OConst value -> Right (constant modulus value)
        OAdd _ _ -> Right (add modulus (arg 0) (arg 1))
        OSub _ _ -> Right (sub modulus (arg 0) (arg 1))
        OMul _ _ -> Right (mul modulus (arg 0) (arg 1))
        ONeg _ -> Right (neg modulus (arg 0))
        OHint _ _ -> Right (var modulus (nWire node))
      if monomialCount poly > maxMonomials
        then Left Failure
          { failTarget = nWire node
          , failAssumptions = []
          , failFreeAdvice = []
          , failNote = Just $
              "the determinacy analysis gave up: expanding this scope exceeds "
              ++ show maxMonomials ++ " monomials. Split it into smaller gadgets, \
                 \or wait for the SMT-backed checker planned for phase 3." }
        else go (Map.insert (nWire node) poly acc) rest

-- | Depth-bounded search. Generalised from phase 2 to accept explicit
-- determined\/nonzero seeds and node-valued targets (a computed result is a
-- node, not an atom, so \"determined\" means all atoms of its polynomial are).
searchWith :: Integer -> [WireId] -> Map.Map WireId Poly
           -> Set.Set WireId -> Set.Set WireId -> [WireId] -> Int -> Branch
           -> Either Failure [[Assumption]]
searchWith modulus advice wirePolys _determined0 _nonzero0 targets = go
  where
    go depth branch0
      | infeasible = Right [brAssumptions branch]
      | null undetermined = Right [brAssumptions branch]
      | depth <= 0 = Left (failureFor branch)
      | otherwise = tryCandidates (candidates branch)
      where
        branch = saturate modulus branch0
        infeasible = any isNonzeroConstant (brEquations branch)
        isNonzeroConstant poly = case asConstant poly of
          Just value -> value /= 0
          Nothing -> False
        undetermined =
          [ t | t <- targets, not (targetKnown wirePolys (brDetermined branch) (brZeroed branch) t) ]

        tryCandidates [] = Left (failureFor branch)
        tryCandidates (w : rest) =
          let zeroBranch = branch
                { brEquations = map (substituteZero w) (brEquations branch)
                , brZeroed = Set.insert w (brZeroed branch)
                , brAssumptions = brAssumptions branch ++ [AssumeZero w]
                , brAssumed = Set.insert w (brAssumed branch) }
              nonzeroBranch = branch
                { brNonzero = Set.insert w (brNonzero branch)
                , brAssumptions = brAssumptions branch ++ [AssumeNonZero w]
                , brAssumed = Set.insert w (brAssumed branch) }
          in case (go (depth - 1) zeroBranch, go (depth - 1) nonzeroBranch) of
               (Right a, Right b) -> Right (a ++ b)
               (Left a, Left b) -> preferDeeper a b `orElse` tryCandidates rest
               (Left a, _) -> Left a `orElse` tryCandidates rest
               (_, Left b) -> Left b `orElse` tryCandidates rest

        failureFor b = Failure
          { failTarget = head (if null undetermined then targets else undetermined)
          , failAssumptions = brAssumptions b
          , failFreeAdvice = [ w | w <- advice, not (w `Set.member` brDetermined b) ]
          , failNote = Nothing }

    candidates branch = blocking ++ [ w | w <- others, not (w `elem` blocking) ]
      where
        mentioned =
          [ w | w <- Set.toList (Set.unions (map atoms (brEquations branch)))
              , w `Set.member` brDetermined branch
              , not (w `Set.member` brAssumed branch) ]
        others = mentioned
        blocking =
          [ w
          | equation <- brEquations branch
          , u <- Set.toList (atoms equation)
          , not (u `Set.member` brDetermined branch)
          , Just (coefficient, remainder) <- [splitLinear modulus u equation]
          , atoms remainder `Set.isSubsetOf` brDetermined branch
          , not (knownNonzeroIn (brNonzero branch) coefficient)
          , w <- Set.toList (atoms coefficient)
          , w `Set.member` brDetermined branch
          , not (w `Set.member` brAssumed branch) ]

    orElse failed alternative = case alternative of
      Right paths -> Right paths
      Left _ -> failed

    preferDeeper a b =
      Left (if length (failAssumptions a) >= length (failAssumptions b) then a else b)

-- | Is target @t@ determined in a branch? For an atom it means @t@ is in the
-- determined set; for a computed node it means every atom of its (branch-
-- specialised) polynomial is determined.
targetKnown :: Map.Map WireId Poly -> Set.Set WireId -> Set.Set WireId -> WireId -> Bool
targetKnown wirePolys determined zeroed t =
  case Map.lookup t wirePolys of
    Nothing -> t `Set.member` determined
    Just poly ->
      let specialised = foldr substituteZero poly (Set.toList zeroed)
      in atoms specialised `Set.isSubsetOf` determined

saturate :: Integer -> Branch -> Branch
saturate modulus branch =
  let next = foldl (tryEquation modulus) branch (brEquations branch)
  in if Set.size (brDetermined next) == Set.size (brDetermined branch)
       then branch
       else saturate modulus next

tryEquation :: Integer -> Branch -> Poly -> Branch
tryEquation modulus branch equation =
  case [ u | u <- Set.toList (atoms equation), not (u `Set.member` brDetermined branch) ] of
    [u] -> case splitLinear modulus u equation of
      Nothing -> branch
      Just (coefficient, remainder)
        | atoms coefficient `Set.isSubsetOf` brDetermined branch
        , atoms remainder `Set.isSubsetOf` brDetermined branch
        , knownNonzero coefficient ->
            branch { brDetermined = Set.insert u (brDetermined branch) }
      _ -> branch
    _ -> branch
  where
    knownNonzero = knownNonzeroIn (brNonzero branch)

knownNonzeroIn :: Set.Set WireId -> Poly -> Bool
knownNonzeroIn nonzeroAtoms poly = case asConstant poly of
  Just value -> value /= 0
  Nothing -> isSingleMonomialIn nonzeroAtoms poly