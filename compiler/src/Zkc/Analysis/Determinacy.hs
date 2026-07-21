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
-- Note what is /not/ required: advice wires need not be determined. In
-- @IsZero@, when @x = 0@ the helper @inv@ genuinely may be anything, and the
-- circuit is still sound because @out@ is pinned regardless. A checker that
-- demanded every advice wire be determined would reject correct code.
--
-- == How it is proved
--
-- Each assertion becomes a polynomial equation @P = 0@ over the circuit's
-- /atoms/ (declared wires and advice wires). Then two rules, applied to
-- exhaustion:
--
--   [Linear propagation] If an equation can be written @c * u + r = 0@ where
--   @u@ is the only undetermined atom, and both @c@ and @r@ are computable
--   from already-determined atoms, and @c@ is known nonzero, then
--   @u = -r/c@ is determined. Fields have no zero divisors, so a product of
--   nonzero values is nonzero — that is what makes @c@ checkable.
--
--   [Case splitting] When propagation stalls, pick a determined atom @w@ and
--   branch on @w = 0@ versus @w /= 0@. In the first branch every monomial
--   containing @w@ vanishes, which often collapses the blocking term; in the
--   second @w@ joins the nonzero set, which unblocks coefficients. If /both/
--   branches determine the outputs, so does the circuit.
--
-- A branch whose equations reduce to a nonzero constant is infeasible — no
-- witness exists there at all — and counts as discharged.
--
-- This is what makes @IsZero@ verifiable. Neither rule alone suffices: the
-- proof needs the split on @x@, and then linear propagation in each branch.
--
-- == Limits, stated plainly
--
-- Splitting is depth-bounded and the analysis is incomplete: a failure means
-- \"not proved\", not \"proved unsound\". Since the pass rejects on failure,
-- incompleteness costs expressiveness, never safety. Polynomial expansion is
-- also exponential in the worst case, so there is a hard cap on size. Both
-- limits are phase-3 work (an SMT escalation path and a smarter
-- representation); neither is hidden from the user.
module Zkc.Analysis.Determinacy
  ( checkDeterminacy
  , Assumption(..)
  , Report(..)
  , Failure(..)
  , maxSplitDepth
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Zkc.Analysis.Poly
import Zkc.Core.Ir
import Zkc.Syntax.Ast (Visibility(..))

-- | How deep the case-split search may go. Three is enough for every gadget
-- in the standard library so far; raising it costs compile time
-- exponentially, so it is a constant rather than a knob.
maxSplitDepth :: Int
maxSplitDepth = 3

-- | Guard against polynomial blow-up. Expanding a deep multiplication tree
-- is exponential, and failing with a clear message beats hanging.
maxMonomials :: Int
maxMonomials = 4096

-- | A case-split hypothesis, carried into diagnostics so a failure can say
-- \"under the assumption x /= 0, ...\".
data Assumption
  = AssumeZero WireId
  | AssumeNonZero WireId
  deriving (Eq, Show)

-- | A successful proof, with the reasoning it used.
data Report = Report
  { repTargets :: [WireId]        -- ^ the outputs that were proved determined
  , repAssumptions :: [[Assumption]]  -- ^ the branches the proof considered
  } deriving (Eq, Show)

data Failure = Failure
  { failTarget :: WireId              -- ^ an output that could not be pinned
  , failAssumptions :: [Assumption]   -- ^ the branch in which it stayed free
  , failFreeAdvice :: [WireId]        -- ^ advice wires still unconstrained there
  , failNote :: Maybe String          -- ^ set when the analysis gave up rather than concluded
  } deriving (Eq, Show)

data Branch = Branch
  { brDetermined :: Set.Set WireId
  , brNonzero :: Set.Set WireId
  , brEquations :: [Poly]
  , brAssumptions :: [Assumption]
  , brAssumed :: Set.Set WireId
  }

-- | Prove that every declared output is determined by the inputs.
checkDeterminacy :: Integer -> Ir -> Either Failure Report
checkDeterminacy modulus ir = do
  wirePolys <- buildPolynomials modulus ir
  let equations =
        [ sub modulus (wirePolys Map.! aLhs a) (wirePolys Map.! aRhs a)
        | a <- irAssertions ir ]
      determined = Set.fromList
        [ iiWire i | i <- irInputs ir, iiVisibility i /= Output ]
      targets = [ iiWire i | i <- irInputs ir, iiVisibility i == Output ]
      root = Branch
        { brDetermined = determined
        , brNonzero = Set.empty
        , brEquations = equations
        , brAssumptions = []
        , brAssumed = Set.empty
        }
  case targets of
    -- No outputs declared: the circuit asserts a relation rather than
    -- computing a function, so there is nothing to determine. This is a
    -- legitimate shape ("I know a, b with a * b = 12"), not an oversight.
    [] -> Right (Report [] [])
    _ -> do
      branches <- search modulus (adviceWires ir) targets maxSplitDepth root
      Right (Report targets branches)

-- | Expand every wire into a polynomial over the atoms.
--
-- Atoms are the declared wires and the advice wires; arithmetic nodes are
-- expanded away, so the equations speak only about values the prover
-- actually chooses.
buildPolynomials :: Integer -> Ir -> Either Failure (Map.Map WireId Poly)
buildPolynomials modulus ir = go initial (irNodes ir)
  where
    initial = Map.fromList $
      (constOneWire, constant modulus 1)
      : [ (iiWire i, var modulus (iiWire i)) | i <- irInputs ir ]

    go acc [] = Right acc
    go acc (node : rest) = do
      let arg index = acc Map.! (opArgs (nOp node) !! index)
      poly <- case nOp node of
        OConst value -> Right (constant modulus value)
        OAdd _ _ -> Right (add modulus (arg 0) (arg 1))
        OSub _ _ -> Right (sub modulus (arg 0) (arg 1))
        OMul _ _ -> Right (mul modulus (arg 0) (arg 1))
        ONeg _ -> Right (neg modulus (arg 0))
        -- An advice wire is an atom: an independent value the prover picks.
        OHint _ _ -> Right (var modulus (nWire node))
      if monomialCount poly > maxMonomials
        then Left Failure
          { failTarget = nWire node
          , failAssumptions = []
          , failFreeAdvice = []
          , failNote = Just $
              "the determinacy analysis gave up: expanding this circuit exceeds "
              ++ show maxMonomials ++ " monomials. Split it into smaller gadgets, \
                 \or wait for the SMT-backed checker planned for phase 3."
          }
        else go (Map.insert (nWire node) poly acc) rest

-- | Depth-bounded search. Returns the assumption paths the proof rested on.
search :: Integer -> [(WireId, HintInfo)] -> [WireId] -> Int -> Branch -> Either Failure [[Assumption]]
search modulus advice targets depth branch0
  | infeasible = Right [brAssumptions branch]        -- no witness here at all
  | null undetermined = Right [brAssumptions branch]
  | depth <= 0 = Left (failureFor branch)
  | otherwise = tryCandidates candidates
  where
    branch = saturate modulus branch0
    infeasible = any isNonzeroConstant (brEquations branch)
    isNonzeroConstant poly = case asConstant poly of
      Just value -> value /= 0
      Nothing -> False

    undetermined = [ t | t <- targets, not (t `Set.member` brDetermined branch) ]

    -- Split on determined atoms the equations actually mention; splitting on
    -- anything else cannot change which coefficients are known nonzero.
    --
    -- Order matters for proof size. An atom that is *blocking* — one sitting
    -- in a coefficient that would otherwise solve an equation — is tried
    -- first, because splitting on it is what unblocks propagation. Trying
    -- atoms in wire order instead finds the same proofs but with spurious
    -- extra cases (@Divide@ needs 2 branches this way and 3 without).
    candidates = blocking ++ [ w | w <- others, not (w `elem` blocking) ]

    mentioned =
      [ w
      | w <- Set.toList (Set.unions (map atoms (brEquations branch)))
      , w `Set.member` brDetermined branch
      , not (w `Set.member` brAssumed branch)
      ]
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
      , not (w `Set.member` brAssumed branch)
      ]

    tryCandidates [] = Left (failureFor branch)
    tryCandidates (w : rest) =
      let zeroBranch = branch
            { brEquations = map (substituteZero w) (brEquations branch)
            , brAssumptions = brAssumptions branch ++ [AssumeZero w]
            , brAssumed = Set.insert w (brAssumed branch)
            }
          nonzeroBranch = branch
            { brNonzero = Set.insert w (brNonzero branch)
            , brAssumptions = brAssumptions branch ++ [AssumeNonZero w]
            , brAssumed = Set.insert w (brAssumed branch)
            }
          recurse = search modulus advice targets (depth - 1)
      in case (recurse zeroBranch, recurse nonzeroBranch) of
           (Right a, Right b) -> Right (a ++ b)
           -- Both branches must succeed. Keep the deeper failure: it is the
           -- more specific explanation of what went wrong.
           (Left a, Left b) -> preferDeeper a b `orElse` tryCandidates rest
           (Left a, _) -> Left a `orElse` tryCandidates rest
           (_, Left b) -> Left b `orElse` tryCandidates rest

    -- If splitting on this atom failed, another atom may still work; only
    -- when every candidate is exhausted is the failure final.
    orElse failed alternative = case alternative of
      Right paths -> Right paths
      Left _ -> failed

    preferDeeper a b =
      Left (if length (failAssumptions a) >= length (failAssumptions b) then a else b)

    failureFor b = Failure
      { failTarget = head (if null undetermined then targets else undetermined)
      , failAssumptions = brAssumptions b
      , failFreeAdvice =
          [ w | (w, _) <- advice, not (w `Set.member` brDetermined b) ]
      , failNote = Nothing
      }

-- | Apply linear propagation until nothing new is determined.
saturate :: Integer -> Branch -> Branch
saturate modulus branch =
  let next = foldl (tryEquation modulus) branch (brEquations branch)
  in if Set.size (brDetermined next) == Set.size (brDetermined branch)
       then branch
       else saturate modulus next

tryEquation :: Integer -> Branch -> Poly -> Branch
tryEquation modulus branch equation =
  case [ u | u <- Set.toList (atoms equation), not (u `Set.member` brDetermined branch) ] of
    -- Exactly one unknown left in this equation: it may be solvable for it.
    [u] -> case splitLinear modulus u equation of
      -- Degree 2 or higher in u: a nonzero leading coefficient no longer
      -- implies a unique root (x^2 = 1 has two), so nothing is learned.
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

-- | Is this coefficient certainly nonzero?
--
-- Either it is a nonzero constant, or it is a single monomial built from
-- atoms already assumed nonzero — fields have no zero divisors, so such a
-- product cannot vanish. Anything else is \"unknown\", and the analysis must
-- case-split rather than guess.
knownNonzeroIn :: Set.Set WireId -> Poly -> Bool
knownNonzeroIn nonzeroAtoms poly = case asConstant poly of
  Just value -> value /= 0
  Nothing -> isSingleMonomialIn nonzeroAtoms poly