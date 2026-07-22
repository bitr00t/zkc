-- | @zkc@ — the circuit compiler CLI.
--
-- > zkc build examples/iszero.zkc -o build/iszero.ir.json
--
-- Pipeline: parse → elaborate → optimize → **prove determinacy** → emit IR.
--
-- The determinacy pass runs after optimization, which is safe because every
-- pass preserves the solution set of the constraint system (constant folding
-- and CSE rewrite how a value is computed, never which assignments satisfy;
-- dead-code elimination only removes nodes no assertion depends on). Running
-- it on the smaller graph keeps the polynomial expansion cheaper.
module Main (main) where

import Control.Monad (forM_, when)
import Data.List (intercalate)
import qualified Data.Set as Set
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.IO
  ( IOMode(ReadMode, WriteMode), hClose, hGetContents, hPutStr, hPutStrLn
  , hSetEncoding, openFile, stderr, stdout, utf8 )

import Zkc.Analysis.Determinacy
import Zkc.Analysis.Smt
  ( Counterexample(..), DeterminacyResult(..), Residual(..), SmtConfig(..)
  , defaultSmtConfig, dialectFromName, escalate, renderCounterexample )
import Zkc.Core.Elaborate (elaborate, Elaborated(..))
import Zkc.Core.Ir
import Zkc.Core.Passes (optimize, renderStats, Stats(..))
import Zkc.Diagnostics
import Zkc.Emit.Json (emitJson)
import Zkc.Field (fieldModulus, knownFields)
import Zkc.Syntax.Parser (parseProgram)

data Options = Options
  { optInput :: FilePath
  , optOutput :: Maybe FilePath
  , optField :: String
  , optOptimize :: Bool
  , optQuiet :: Bool
  , optExplain :: Bool
  , optSmt :: SmtConfig
  }

defaultOptions :: FilePath -> Options
defaultOptions input = Options
  { optInput = input
  , optOutput = Nothing
  , optField = "bn254"
  , optOptimize = True
  , optQuiet = False
  , optExplain = False
  , optSmt = defaultSmtConfig
  }

main :: IO ()
main = do
  -- Source files are UTF-8 regardless of the user's locale.
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  args <- getArgs
  case args of
    ("build" : input : rest) -> case parseOptions (defaultOptions input) rest of
      Left message -> hPutStrLn stderr ("error: " ++ message) >> exitFailure
      Right options -> run options
    _ -> usage >> exitFailure

parseOptions :: Options -> [String] -> Either String Options
parseOptions opts [] = Right opts
parseOptions opts ("-o" : path : rest) = parseOptions opts { optOutput = Just path } rest
parseOptions opts ("--field" : name : rest) = parseOptions opts { optField = name } rest
parseOptions opts ("--no-opt" : rest) = parseOptions opts { optOptimize = False } rest
parseOptions opts ("--quiet" : rest) = parseOptions opts { optQuiet = True } rest
parseOptions opts ("--explain" : rest) = parseOptions opts { optExplain = True } rest
parseOptions opts ("--no-smt" : rest) =
  parseOptions opts { optSmt = (optSmt opts) { smtEnabled = False } } rest
parseOptions opts ("--smt-solver" : command : rest) =
  parseOptions opts { optSmt = (optSmt opts) { smtCommand = command } } rest
parseOptions opts ("--smt-dialect" : name : rest) =
  case dialectFromName name of
    Just dialect -> parseOptions opts { optSmt = (optSmt opts) { smtDialect = dialect } } rest
    Nothing -> Left ("unknown SMT dialect '" ++ name ++ "'; known: ff, int")
parseOptions opts ("--smt-timeout" : seconds : rest) =
  case reads seconds of
    [(n, "")] -> parseOptions opts { optSmt = (optSmt opts) { smtTimeout = n } } rest
    _ -> Left ("--smt-timeout expects a number of seconds, got '" ++ seconds ++ "'")
parseOptions opts ("--dump-smt" : path : rest) =
  parseOptions opts { optSmt = (optSmt opts) { smtDump = Just path } } rest
parseOptions _ (flag : _) = Left ("unknown option: " ++ flag)

run :: Options -> IO ()
run opts = do
  source <- readFileUtf8 (optInput opts)
  case prepare opts source of
    Left problem -> do
      hPutStr stderr (render (optInput opts) source problem)
      exitFailure
    Right (elab, modulus) -> do
      verdict <- proveDeterminacy opts modulus elab
      let (ir, stats) =
            if optOptimize opts then optimize (elabIr elab)
                                else (elabIr elab, Stats 0 0 0)
      case verdict of
        VProved report viaSmt -> do
          let json = emitJson report ir
          case optOutput opts of
            Nothing -> putStrLn json
            Just path -> writeFileUtf8 path json
          when (not (optQuiet opts)) $ do
            hPutStrLn stderr $
              "compiled '" ++ irName ir ++ "' over " ++ irField ir
              ++ ": " ++ show (length (irInputs ir)) ++ " inputs, "
              ++ show (length (irNodes ir)) ++ " nodes, "
              ++ show (length (irAssertions ir)) ++ " assertions"
            when (optOptimize opts) $
              hPutStrLn stderr ("  optimizer: " ++ renderStats stats)
            hPutStrLn stderr ("  determinacy: " ++ summariseReport ir report
                              ++ (if viaSmt then " (via SMT escalation)" else ""))
            when (optExplain opts) (explain ir report)
          exitSuccess

        -- The decidable core said no and escalation was switched off: exactly
        -- the phase-2 message, so `--no-smt` is a true rollback.
        VRejected failure -> do
          hPutStr stderr (render (optInput opts) source (determinacyDiagnostic failure))
          exitFailure

        -- The solver produced the attack. This is worth far more than a
        -- rejection: it is the forgery, ready to reproduce.
        VRefuted cex -> do
          hPutStr stderr (render (optInput opts) source (refutationDiagnostic modulus cex))
          exitFailure

        -- Honest incompleteness.
        VUnknown residual -> do
          hPutStr stderr (render (optInput opts) source (residualDiagnostic residual))
          exitFailure

-- | Everything up to (but not including) the determinacy proof, which is the
-- last purely-functional step.
prepare :: Options -> String -> Either Diagnostic (Elaborated, Integer)
prepare opts source = do
  program <- parseProgram source
  elab <- elaborate (optField opts) program
  modulus <- case fieldModulus (optField opts) of
    Just p -> Right p
    Nothing -> Left $ withHelp ("known fields: " ++ unwords (map fst knownFields))
      $ diag ("unknown field '" ++ optField opts ++ "'; the determinacy analysis \
              \needs its modulus to decide whether a coefficient is nonzero")
  Right (elab, modulus)

-- | What the compiler concluded about determinacy.
data Verdict
  = VProved Report Bool         -- ^ proved; the flag records whether SMT was needed
  | VRefuted Counterexample     -- ^ genuinely under-constrained, with the forgery
  | VUnknown Residual           -- ^ the analysis could not decide, and says so
  | VRejected ProgramFailure    -- ^ decidable core said no, escalation disabled

-- | Prove determinacy, escalating to a solver when the decidable core stalls.
--
-- The decidable core stays the fast path — it answers the common gadget in
-- milliseconds and is never skipped. Only when it stalls does a solver see the
-- question, and then only for the one scope that stalled, which is what
-- compositional proving (Workstream A) bought us: the query is one small
-- gadget, never the inlined whole.
--
-- When the solver discharges a /gadget/, its result is fed back as an assumed
-- summary and the compositional proof resumes — so one escalation can unblock
-- every call site at once. The fuel bounds that loop: each gadget can be
-- assumed at most once.
proveDeterminacy :: Options -> Integer -> Elaborated -> IO Verdict
proveDeterminacy opts modulus elab = go Set.empty (length (elabGadgetBodies elab) + 1)
  where
    config = optSmt opts
    gadgets = elabGadgetBodies elab
    circuit = elabCircuitBody elab

    go assumed fuel =
      case checkProgramWith modulus assumed gadgets circuit of
        Right report -> pure (VProved report (not (Set.null assumed)))
        Left failure
          | not (smtEnabled config) -> pure (VRejected failure)
          | fuel <= (0 :: Int) -> pure $ VUnknown Residual
              { rsScope = pfScope failure
              , rsReason = "escalation stopped making progress"
              , rsQueryPath = Nothing
              }
          | otherwise -> do
              result <- escalate config modulus failure
              case result of
                Refuted cex -> pure (VRefuted cex)
                Unknown residual -> pure (VUnknown residual)
                Proved report
                  | pfIsGadget failure ->
                      go (Set.insert (pfScope failure) assumed) (fuel - 1)
                  | otherwise -> pure (VProved report True)

-- Determinacy reporting ------------------------------------------------

summariseReport :: Ir -> Report -> String
summariseReport ir report = case repTargets report of
  [] -> "no outputs declared, nothing to prove"
  targets ->
    show (length targets) ++ " output(s) proved determined ("
    ++ unwords (map (nameOf ir) targets) ++ "), "
    ++ show (length (repAssumptions report)) ++ " case(s)"

explain :: Ir -> Report -> IO ()
explain ir report = forM_ (repAssumptions report) $ \assumptions ->
  hPutStrLn stderr $ "    case " ++ describeCase ir assumptions

describeCase :: Ir -> [Assumption] -> String
describeCase ir assumptions
  | null assumptions = "(no assumptions needed)"
  | otherwise = intercalate ", " [ renderAssumption ir a | a <- assumptions ]

renderAssumption :: Ir -> Assumption -> String
renderAssumption ir a = case a of
  AssumeZero w -> nameOf ir w ++ " == 0"
  AssumeNonZero w -> nameOf ir w ++ " != 0"

nameOf :: Ir -> WireId -> String
nameOf ir wire =
  case [ iiName i | i <- irInputs ir, iiWire i == wire ] of
    (name : _) -> name
    [] -> case [ hiName info | (w, info) <- adviceWires ir, w == wire ] of
      (name : _) -> name
      [] -> "wire" ++ show wire

-- | Naming inside a failing scope.
--
-- A gadget body numbers its wires locally, so resolving them against the
-- circuit's IR would print the wrong names. The failure carries its own body
-- precisely so this can be right.
nameInBody :: Body -> WireId -> String
nameInBody body wire =
  case [ iiName i | i <- bodyAtoms body, iiWire i == wire ] of
    (name : _) -> name
    [] -> case [ hiName info | Node w (OHint info _) <- bodyNodes body, w == wire ] of
      (name : _) -> name
      [] -> "wire" ++ show wire

renderAssumptionIn :: Body -> Assumption -> String
renderAssumptionIn body a = case a of
  AssumeZero w -> nameInBody body w ++ " == 0"
  AssumeNonZero w -> nameInBody body w ++ " != 0"

-- | Turn a failed determinacy proof into an error a circuit author can act on.
determinacyDiagnostic :: ProgramFailure -> Diagnostic
determinacyDiagnostic problem = case failNote failure of
  Just note -> withNotes [note] (diag ("the determinacy analysis could not finish" ++ context))
  Nothing ->
    withHelp ("add a constraint that forces '" ++ target
              ++ "' in this case, then recompile")
    $ withNotes (assumptionNote ++ adviceNote ++ [conclusion])
    $ diagAt line ("output '" ++ target ++ "' is not determined by the inputs" ++ context)
  where
    failure = pfFailure problem
    body = pfBody problem
    context
      | pfIsGadget problem = " of gadget '" ++ pfScope problem ++ "'"
      | otherwise = ""
    target = nameInBody body (failTarget failure)
    line = case [ iiLine i | i <- bodyAtoms body, iiWire i == failTarget failure, iiLine i > 0 ] of
      (l : _) -> l
      [] -> 1

    assumptionNote = case failAssumptions failure of
      [] -> ["the constraints admit more than one value of '" ++ target
             ++ "' for the same inputs"]
      assumptions ->
        [ "under the assumption "
          ++ intercalate " and " (map (renderAssumptionIn body) assumptions)
          ++ ", the constraints admit more than one value of '" ++ target ++ "'" ]

    adviceNote = case failFreeAdvice failure of
      [] -> []
      wires ->
        [ "the prover also chooses the advice "
          ++ (if length wires == 1 then "value " else "values ")
          ++ unwords [ "'" ++ nameInBody body w ++ "'" | w <- wires ] ++ " freely" ]

    conclusion =
      "so two witnesses can agree on every input and still disagree on '"
      ++ target ++ "' — the prover picks which one to prove"

-- | A refutation: not \"I could not prove this\" but \"here is the attack\".
refutationDiagnostic :: Integer -> Counterexample -> Diagnostic
refutationDiagnostic modulus cex =
  withHelp "add a constraint that rules out one of these two witnesses"
  $ withNotes (renderCounterexample modulus cex)
  $ diagAt (cxLine cex) ("'" ++ cxScope cex ++ "' is under-constrained — "
          ++ "the solver constructed a forgery")

-- | Honest incompleteness: neither proved nor refuted.
residualDiagnostic :: Residual -> Diagnostic
residualDiagnostic residual =
  withHelp helpText
  $ withNotes
      [ "this is not a claim that the circuit is wrong: the analysis ran out of"
      , "room before it could decide either way"
      ]
  $ diag ("could not decide whether '" ++ rsScope residual
          ++ "' is determined: " ++ rsReason residual)
  where
    helpText = case rsQueryPath residual of
      Just path -> "the query was written to " ++ path ++ "; try a longer \
                   \--smt-timeout, or a solver with finite-field support"
      Nothing -> "try a longer --smt-timeout, --dump-smt to inspect the query, \
                 \or a solver with finite-field support"

-- IO helpers -----------------------------------------------------------

readFileUtf8 :: FilePath -> IO String
readFileUtf8 path = do
  handle <- openFile path ReadMode
  hSetEncoding handle utf8
  hGetContents handle   -- lazy read; the handle closes when fully consumed

writeFileUtf8 :: FilePath -> String -> IO ()
writeFileUtf8 path contents = do
  handle <- openFile path WriteMode
  hSetEncoding handle utf8
  hPutStr handle contents
  hClose handle

usage :: IO ()
usage = mapM_ (hPutStrLn stderr)
  [ "zkc — zero-knowledge circuit compiler (phase 3)"
  , ""
  , "usage:"
  , "  zkc build <file.zkc> [-o <out.json>] [--field <name>] [--no-opt]"
  , "                       [--explain] [--quiet]"
  , "                       [--no-smt] [--smt-solver <cmd>] [--smt-dialect ff|int]"
  , "                       [--smt-timeout <seconds>] [--dump-smt <path>]"
  , ""
  , "  --explain       print the case splits the determinacy proof used"
  , ""
  , "  When the decidable determinacy check stalls, the residual question is"
  , "  escalated to an SMT solver, which can refute (printing the forgery) as"
  , "  well as prove. The escalation only ever sees the one scope that stalled."
  , ""
  , "  --no-smt        skip escalation entirely (exact phase-2 behaviour)"
  , "  --smt-solver    solver executable (default: cvc5)"
  , "  --smt-dialect   ff  = QF_FF, field arithmetic natively (default)"
  , "                  int = QF_NIA, integers with explicit mod, for solvers"
  , "                        without finite-field support"
  , "  --dump-smt      write the query to a file for inspection"
  , ""
  , "Emits the Core IR as JSON. Feed it to the Rust backend to lower, solve,"
  , "prove and verify."
  ]