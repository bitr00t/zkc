-- | SMT escalation: what to do when the decidable core gives up.
--
-- == Why escalate at all
--
-- Phase 2's answer to \"I could not prove this\" was to reject. That collapses
-- two very different situations into one message: /this circuit is genuinely
-- under-constrained/ and /my incomplete analysis could not decide/. The first
-- is a security bug in the user's code; the second is a limitation of mine.
-- Telling them apart is the whole of Workstream B, and the payoff is that the
-- first case can be reported with __the actual attack__ rather than a shrug.
--
-- == The query: uniqueness as self-composition
--
-- Determinacy is a two-copy property. Take two witnesses @w@ and @w'@ over the
-- field, assert that both satisfy every constraint, assert they agree on every
-- input, and ask whether they can still __disagree on an output__:
--
--   * __unsat__ — no such pair exists, so the outputs are a function of the
--     inputs: /proved/.
--   * __sat__ — the model /is/ the forgery: two witnesses, same inputs,
--     different output. Print it: /refuted/.
--   * __unknown__ / timeout — say so honestly: /unknown/.
--
-- This is exactly the artifact the phase-0 forgery demo built by hand, now
-- derived automatically from the circuit.
--
-- == Two dialects, one interface
--
-- Field arithmetic has a purpose-built SMT theory, @QF_FF@, designed for this
-- job; it reasons over the field directly (Gröbner bases) instead of through a
-- modular encoding. It is the right target and the default.
--
-- It is also not universally available: @QF_FF@ needs a solver built with
-- finite-field support, which stock builds often omit. So the query is emitted
-- through a 'Dialect', and a second dialect encodes the same question as
-- integer arithmetic with explicit @mod@ — accepted by any @QF_NIA@ solver.
-- The integer encoding is weaker in a specific and predictable way: nonlinear
-- integer arithmetic is undecidable, so solvers find /counterexamples/ readily
-- but time out trying to prove their absence. Which is fine, because the
-- three-valued result already has an honest place to put that: 'Unknown'.
--
-- == What a solver's answer is allowed to mean
--
-- One asymmetry is load-bearing. When a scope contains gadget instances, their
-- results appear as free atoms while the constraints pinning them down stay in
-- the callee (that is what makes composition cheap). The system handed to the
-- solver is then a __relaxation__ of the real circuit — it admits at least
-- every witness the real one does. So:
--
--   * @unsat@ on a relaxation implies @unsat@ on the real circuit: a __proof
--     carries over__;
--   * @sat@ may be an artifact of the omitted constraints: a __refutation does
--     not__, and is downgraded to 'Unknown'.
--
-- Getting this backwards would let the compiler accuse correct code of being
-- forgeable, which is worse than saying nothing.
module Zkc.Analysis.Smt
  ( Dialect(..)
  , SmtConfig(..)
  , defaultSmtConfig
  , dialectFromName
  , defaultSolverArgs
  , DeterminacyResult(..)
  , Counterexample(..)
  , Residual(..)
  , Query(..)
  , buildQuery
  , escalate
  , renderCounterexample
  , SolverAnswer(..)
  , parseAnswer
  ) where

import Control.Exception (IOException, try)
import Data.Char (isDigit, isSpace)
import Data.List (intercalate, sortOn)
import qualified Data.Map.Strict as Map
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

import Zkc.Analysis.Determinacy
import Zkc.Analysis.Poly (Poly, terms)
import Zkc.Core.Ir (WireId, Body(..), IrInput(..))

-- Configuration ----------------------------------------------------------

-- | How to phrase the question.
data Dialect
  = FiniteField
    -- ^ @QF_FF@: field elements and field operations, natively. Correct and
    -- complete for this problem, given a solver that supports it.
  | IntegerMod
    -- ^ @QF_NIA@: integers in @[0, p)@ with explicit @mod@. Works with any
    -- nonlinear-integer solver; good at finding counterexamples, poor at
    -- proving their absence.
  deriving (Eq, Show)

dialectFromName :: String -> Maybe Dialect
dialectFromName name = case name of
  "ff" -> Just FiniteField
  "field" -> Just FiniteField
  "int" -> Just IntegerMod
  "integer" -> Just IntegerMod
  _ -> Nothing

data SmtConfig = SmtConfig
  { smtEnabled :: Bool
  , smtCommand :: String        -- ^ solver executable
  , smtArgs :: Maybe [String]   -- ^ explicit args; 'Nothing' picks per-solver defaults
  , smtDialect :: Dialect
  , smtTimeout :: Int           -- ^ seconds
  , smtDump :: Maybe FilePath   -- ^ write the query here for inspection
  }

defaultSmtConfig :: SmtConfig
defaultSmtConfig = SmtConfig
  { smtEnabled = True
  , smtCommand = "cvc5"
  , smtArgs = Nothing
  , smtDialect = FiniteField
  , smtTimeout = 10
  , smtDump = Nothing
  }

-- | Timeout flags differ per solver and there is no standard for them, so the
-- few we know about are spelled out and anything else gets none (the caller can
-- always pass args explicitly).
defaultSolverArgs :: String -> Int -> [String]
defaultSolverArgs command seconds
  | command `endsWith` "cvc5" = ["--lang=smt2", "--tlimit=" ++ show (seconds * 1000)]
  | command `endsWith` "z3" = ["-smt2", "-T:" ++ show seconds]
  | otherwise = []
  where
    endsWith haystack needle =
      let n = length needle
          h = length haystack
      in n <= h && drop (h - n) haystack == needle

-- Results ----------------------------------------------------------------

-- | The three-valued verdict that replaces phase 2's binary reject.
data DeterminacyResult
  = Proved Report
  | Refuted Counterexample
  | Unknown Residual

-- | Two witnesses that agree on every input and disagree on an output. The
-- forgery, in the user's own names.
data Counterexample = Counterexample
  { cxScope :: String
  , cxLine :: Int                         -- ^ where the scope is declared
  , cxInputs :: [(String, Integer)]       -- ^ agreed by both witnesses
  , cxWitnessA :: [(String, Integer)]     -- ^ the rest of witness 1
  , cxWitnessB :: [(String, Integer)]     -- ^ the rest of witness 2
  , cxTargets :: [(String, Integer, Integer)] -- ^ output, value in A, value in B
  }

-- | The analysis could not decide, and says why.
data Residual = Residual
  { rsScope :: String
  , rsReason :: String
  , rsQueryPath :: Maybe FilePath
  }

-- Query construction (pure) ----------------------------------------------

data Query = Query
  { qText :: String              -- ^ SMT-LIB2 source
  , qAtomNames :: [(String, (WireId, String))]
    -- ^ solver variable -> (wire, source name); used to read the model back
  , qCopyOf :: Map.Map String Int -- ^ solver variable -> 1 or 2
  }

-- | Variable naming is mechanical so the model can be read back without
-- carrying a symbol table into the solver and out again.
atomVar :: Int -> WireId -> String
atomVar copy wire = "w" ++ show wire ++ "_" ++ show copy

-- | Build the self-composition query for one scope.
buildQuery :: Integer -> Dialect -> String -> BodySystem -> Query
buildQuery modulus dialect scope system = Query
  { qText = unlines (header ++ declarations ++ constraintsA ++ constraintsB
                     ++ agreement ++ nonzero ++ [disagreement] ++ footer)
  , qAtomNames =
      [ (atomVar copy wire, (wire, name))
      | copy <- [1, 2], (wire, name) <- bsAtoms system ]
  , qCopyOf = Map.fromList
      [ (atomVar copy wire, copy) | copy <- [1, 2], (wire, _) <- bsAtoms system ]
  }
  where
    allAtoms = bsAtoms system

    -- The query is piped to another process, so it stays strictly ASCII: the
    -- pipe's encoding is not ours to choose, and SMT-LIB2 has no need of more.
    preamble =
      [ "; determinacy of " ++ ascii scope ++ ", as self-composition:"
      , "; two witnesses, equal on every input - can they differ on an output?"
      ]

    header = case dialect of
      FiniteField -> preamble ++
        [ "(set-logic QF_FF)"
        , "(set-option :produce-models true)"
        , "(define-sort F () (_ FiniteField " ++ show modulus ++ "))"
        ]
      IntegerMod -> preamble ++
        [ "(set-logic QF_NIA)"
        , "(set-option :produce-models true)"
        , "(define-fun P () Int " ++ show modulus ++ ")"
        ]

    declarations = concat
      [ declare (atomVar copy wire) | copy <- [1, 2], (wire, _) <- allAtoms ]

    declare name = case dialect of
      FiniteField -> ["(declare-fun " ++ name ++ " () F)"]
      IntegerMod ->
        [ "(declare-fun " ++ name ++ " () Int)"
        , "(assert (and (>= " ++ name ++ " 0) (< " ++ name ++ " P)))"
        ]

    constraintsA = [ equationAssert 1 p | p <- bsEquations system ]
    constraintsB = [ equationAssert 2 p | p <- bsEquations system ]

    equationAssert copy poly = case dialect of
      FiniteField ->
        "(assert (= " ++ renderPoly dialect copy poly ++ " " ++ ffLit 0 ++ "))"
      IntegerMod ->
        "(assert (= (mod " ++ renderPoly dialect copy poly ++ " P) 0))"

    -- The witnesses agree on every input.
    agreement =
      [ "(assert (= " ++ atomVar 1 w ++ " " ++ atomVar 2 w ++ "))"
      | w <- bsInputs system ]

    -- Preconditions the scope was proved under must hold in both copies,
    -- or the solver would "refute" a gadget by violating its own contract.
    nonzero = concat
      [ [ notZero (atomVar copy w) | copy <- [1, 2] ] | w <- bsNonzero system ]

    notZero name = case dialect of
      FiniteField -> "(assert (not (= " ++ name ++ " " ++ ffLit 0 ++ ")))"
      IntegerMod -> "(assert (not (= (mod " ++ name ++ " P) 0)))"

    -- ...and yet some output differs. This is the question.
    disagreement =
      let clauses =
            [ differs (renderPoly dialect 1 poly) (renderPoly dialect 2 poly)
            | (_, _, poly) <- bsTargets system ]
      in case clauses of
           [] -> "(assert false) ; no outputs: nothing could differ"
           [only] -> "(assert " ++ only ++ ")"
           many -> "(assert (or " ++ unwords many ++ "))"

    differs a b = case dialect of
      FiniteField -> "(not (= " ++ a ++ " " ++ b ++ "))"
      IntegerMod -> "(not (= (mod " ++ a ++ " P) (mod " ++ b ++ " P)))"

    footer =
      [ "(check-sat)"
      , "(get-value (" ++ unwords [ atomVar copy w | copy <- [1, 2], (w, _) <- allAtoms ] ++ "))"
      ]

    ffLit n = "(as ff" ++ show (n :: Integer) ++ " F)"

-- | Render a polynomial as an SMT-LIB2 expression in the given copy.
renderPoly :: Dialect -> Int -> Poly -> String
renderPoly dialect copy poly = case terms poly of
  [] -> zero
  [single] -> renderTerm single
  many -> nary plus (map renderTerm many)
  where
    (zero, plus, times, literal) = case dialect of
      FiniteField -> ("(as ff0 F)", "ff.add", "ff.mul", \c -> "(as ff" ++ show c ++ " F)")
      IntegerMod -> ("0", "+", "*", show)

    renderTerm (mono, coeff) =
      let factors = concat [ replicate power (atomVar copy atom)
                           | (atom, power) <- Map.toList mono ]
      in case (factors, coeff) of
           ([], _) -> literal coeff
           (_, 1) -> nary times factors
           _ -> nary times (literal coeff : factors)

    nary _ [x] = x
    nary op xs = "(" ++ op ++ " " ++ unwords xs ++ ")"

-- Solver invocation (IO) -------------------------------------------------

data SolverAnswer
  = AnswerSat [(String, Integer)]
  | AnswerUnsat
  | AnswerUnknown String
  deriving (Eq, Show)

-- | Escalate one open obligation to the solver.
escalate :: SmtConfig -> Integer -> ProgramFailure -> IO DeterminacyResult
escalate config modulus failure =
  case bodySystem modulus (pfBody failure) of
    Left inner -> pure $ Unknown Residual
      { rsScope = scope
      , rsReason = "the scope could not even be expressed as polynomials: "
                   ++ maybe "expansion limit reached" id (failNote inner)
      , rsQueryPath = Nothing
      }
    Right system -> do
      let query = buildQuery modulus (smtDialect config) scope system
      dumped <- dumpQuery config query
      answer <- runSolver config (qText query)
      pure (interpret scope line system dumped answer)
  where
    scope = pfScope failure
    line = case [ l | i <- bodyAtoms (pfBody failure), let l = iiLine i, l > 0 ] of
      (l : _) -> l
      [] -> 1

dumpQuery :: SmtConfig -> Query -> IO (Maybe FilePath)
dumpQuery config query = case smtDump config of
  Nothing -> pure Nothing
  Just path -> do
    written <- try (writeFile path (qText query)) :: IO (Either IOException ())
    pure (either (const Nothing) (const (Just path)) written)

runSolver :: SmtConfig -> String -> IO SolverAnswer
runSolver config text = do
  let args = maybe (defaultSolverArgs (smtCommand config) (smtTimeout config))
                   id (smtArgs config)
  outcome <- try (readProcessWithExitCode (smtCommand config) (args ++ ["/dev/stdin"]) text)
  case outcome :: Either IOException (ExitCode, String, String) of
    Left err -> pure $ AnswerUnknown
      ("could not run solver '" ++ smtCommand config ++ "': " ++ show err)
    Right (_, out, err) ->
      -- Solvers report unsat via stdout and exit codes vary, so the text is
      -- what we trust; a nonzero exit with a usable answer is still an answer.
      case parseAnswer out of
        AnswerUnknown reason
          | not (null (trim err)) -> pure (AnswerUnknown (reason ++ "; " ++ trim err))
        parsed -> pure parsed

interpret :: String -> Int -> BodySystem -> Maybe FilePath
          -> SolverAnswer -> DeterminacyResult
interpret scope line system dumped answer = case answer of
  -- No pair of witnesses can agree on inputs and differ on an output. Sound
  -- even when the system is a relaxation, so this proves the real circuit.
  AnswerUnsat -> Proved (Report [ w | (w, _, _) <- bsTargets system ] [[]])

  AnswerSat _ | not (bsSelfContained system) -> Unknown Residual
    { rsScope = scope
    , rsReason =
        "the solver found two witnesses, but this scope instantiates gadgets \
        \whose internal constraints were not expanded, so the pair may not be \
        \realisable in the real circuit; refusing to call it a forgery"
    , rsQueryPath = dumped
    }

  AnswerSat bindings -> case counterexampleFrom scope line system bindings of
    Just cex -> Refuted cex
    Nothing -> Unknown Residual
      { rsScope = scope
      , rsReason = "the solver answered sat but its model could not be read back"
      , rsQueryPath = dumped
      }

  AnswerUnknown reason -> Unknown Residual
    { rsScope = scope, rsReason = reason, rsQueryPath = dumped }

-- | Turn a model into the forgery, in source-level names.
counterexampleFrom :: String -> Int -> BodySystem -> [(String, Integer)]
                   -> Maybe Counterexample
counterexampleFrom scope line system bindings
  | null differing = Nothing
  | otherwise = Just Counterexample
      { cxScope = scope
      , cxLine = line
      , cxInputs = [ (name, v) | (w, name) <- bsAtoms system
                   , w `elem` bsInputs system, Just v <- [value 1 w] ]
      , cxWitnessA = rest 1
      , cxWitnessB = rest 2
      , cxTargets = differing
      }
  where
    table = Map.fromList bindings
    value copy wire = Map.lookup (atomVar copy wire) table

    evaluate copy poly = sum
      [ coeff * product [ maybe 0 id (value copy atom) ^ power
                        | (atom, power) <- Map.toList mono ]
      | (mono, coeff) <- terms poly ]

    differing =
      [ (name, a, b)
      | (_, name, poly) <- bsTargets system
      , let a = evaluate 1 poly
      , let b = evaluate 2 poly
      , a /= b ]

    -- Inputs are shown once as agreed, targets once as disagreeing; what is
    -- left is the free choice the prover actually exploits.
    targetWires = [ w | (w, _, _) <- bsTargets system ]
    rest copy =
      [ (name, v)
      | (w, name) <- bsAtoms system
      , not (w `elem` bsInputs system)
      , not (w `elem` targetWires)
      , Just v <- [value copy w] ]

-- | The forgery as lines a circuit author can read.
renderCounterexample :: Integer -> Counterexample -> [String]
renderCounterexample modulus cex =
  [ "two witnesses satisfy every constraint and agree on all inputs:" ]
  ++ [ "    " ++ name ++ " = " ++ signed v | (name, v) <- sortOn fst (cxInputs cex) ]
  ++ [ "but disagree on:" ]
  ++ [ "    " ++ name ++ " = " ++ signed a ++ "   vs   " ++ name ++ " = " ++ signed b
     | (name, a, b) <- cxTargets cex ]
  ++ describe "witness 1 chooses" (cxWitnessA cex)
  ++ describe "witness 2 chooses" (cxWitnessB cex)
  ++ [ "the prover picks whichever it prefers, and proves it" ]
  where
    describe _ [] = []
    describe label values =
      [ "  " ++ label ++ ": "
        ++ intercalate ", " [ name ++ " = " ++ signed v | (name, v) <- sortOn fst values ] ]
    -- Field elements just below the modulus read better as small negatives.
    signed v
      | v > modulus `div` 2 = show (v - modulus)
      | otherwise = show v

-- Answer parsing (pure) --------------------------------------------------

-- | Read a solver's reply: the @sat@/@unsat@/@unknown@ line, and, when
-- satisfiable, the @get-value@ model.
parseAnswer :: String -> SolverAnswer
parseAnswer output
  | any (== "unsat") tokens = AnswerUnsat
  | any (== "sat") tokens = AnswerSat (bindings (parseSexps output))
  | any (== "unknown") tokens = AnswerUnknown "the solver returned unknown"
  | any (== "timeout") tokens = AnswerUnknown "the solver timed out"
  | otherwise = AnswerUnknown ("unrecognised solver output: " ++ trim (firstLine output))
  where
    tokens = words (map (\c -> if c `elem` "()" then ' ' else c) output)
    firstLine = takeWhile (/= '\n')

-- | Extract @(name value)@ pairs from a @get-value@ response.
bindings :: [Sexp] -> [(String, Integer)]
bindings = concatMap go
  where
    go (List items) = case items of
      [Atom name, v] | Just n <- numeric v -> [(name, n)]
      _ -> concatMap go items
    go _ = []

numeric :: Sexp -> Maybe Integer
numeric sexp = case sexp of
  Atom text -> literalValue text
  -- (- 5), and the field-literal form (as ff5 F)
  List [Atom "-", Atom digits] | all isDigit digits -> Just (negate (read digits))
  List (Atom "as" : Atom text : _) -> literalValue text
  _ -> Nothing
  where
    literalValue text
      | all isDigit text && not (null text) = Just (read text)
      -- cvc5 prints field literals as #fVALUEmMODULUS
      | take 2 text == "#f" =
          let digits = takeWhile isDigit (drop 2 text)
          in if null digits then Nothing else Just (read digits)
      | take 2 text == "ff" =
          let digits = takeWhile isDigit (drop 2 text)
          in if null digits then Nothing else Just (read digits)
      | otherwise = Nothing

data Sexp = Atom String | List [Sexp]
  deriving (Eq, Show)

parseSexps :: String -> [Sexp]
parseSexps = fst . many
  where
    many input = case dropWhile isSpace input of
      "" -> ([], "")
      ')' : rest -> ([], rest)
      rest ->
        let (sexp, rest') = one rest
            (more, rest'') = many rest'
        in (sexp : more, rest'')

    one ('(' : rest) =
      let (items, rest') = many rest
      in (List items, rest')
    one input =
      let (text, rest) = span (\c -> not (isSpace c) && c /= '(' && c /= ')') input
      in (Atom text, rest)

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- | Keep text inside the ASCII range. Only comments can carry a name the user
-- chose, and a comment is never worth failing a pipe over.
ascii :: String -> String
ascii = map (\c -> if fromEnum c < 128 then c else '?')