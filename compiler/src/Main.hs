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
import System.Environment (getArgs, lookupEnv)
import System.IO.Error (tryIOError)
import System.Exit (exitFailure, exitSuccess)
import System.IO
  ( IOMode(ReadMode, WriteMode), hClose, hGetContents, hPutStr, hPutStrLn
  , hSetEncoding, openFile, stderr, stdout, utf8 )

import Zkc.Analysis.Determinacy
import Zkc.Analysis.Smt
  ( Counterexample(..), DeterminacyResult(..), Residual(..), SmtConfig(..)
  , defaultSmtConfig, dialectFromName, escalate )
import Zkc.Core.Elaborate (elaborate, Elaborated(..))
import Zkc.Core.Ir
import Zkc.Core.Passes (optimize, renderStats, Stats(..))
import Zkc.Diagnose (determinacyDiagnostic, refutationDiagnostic, residualDiagnostic)
import Zkc.Lsp (runLsp)
import Zkc.Reference (renderReference)
import Zkc.Diagnostics
import Zkc.Emit.Json (emitJson)
import Zkc.Field (fieldModulus, knownFields)
import Zkc.Syntax.Ast (Program(..), UseDecl(..), GadgetDef(..))
import Zkc.Syntax.Parser (parseProgram, parseGadgets)

-- | How diagnostics are printed: for a human to read, or as one JSON object
-- per diagnostic for an editor or language server to consume.
data ErrorFormat = HumanErrors | JsonErrors

data Options = Options
  { optInput :: FilePath
  , optOutput :: Maybe FilePath
  , optField :: String
  , optOptimize :: Bool
  , optQuiet :: Bool
  , optExplain :: Bool
  , optSmt :: SmtConfig
  , optErrorFormat :: ErrorFormat
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
  , optErrorFormat = HumanErrors
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
    ("doc" : input : rest) -> case parseOptions (defaultOptions input) rest of
      Left message -> hPutStrLn stderr ("error: " ++ message) >> exitFailure
      Right options -> runDoc options
    ("lsp" : _) -> runLsp
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
parseOptions opts ("--error-format" : name : rest) =
  case name of
    "human" -> parseOptions opts { optErrorFormat = HumanErrors } rest
    "json"  -> parseOptions opts { optErrorFormat = JsonErrors } rest
    _ -> Left ("unknown --error-format '" ++ name ++ "'; known: human, json")
parseOptions _ (flag : _) = Left ("unknown option: " ++ flag)

-- | Print a diagnostic in the configured format: human-readable text, or a
-- single JSON object (the machine-readable form phase 6 adds).
emitDiagnostic :: Options -> String -> Diagnostic -> IO ()
emitDiagnostic opts source d = case optErrorFormat opts of
  HumanErrors -> hPutStr stderr (render (optInput opts) source d)
  JsonErrors  -> hPutStrLn stderr (renderJson d)

run :: Options -> IO ()
run opts = do
  source <- readFileUtf8 (optInput opts)
  prepared <- prepareIO opts source
  case prepared of
    Left problem -> do
      emitDiagnostic opts source problem
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
          emitDiagnostic opts source (determinacyDiagnostic failure)
          exitFailure

        -- The solver produced the attack. This is worth far more than a
        -- rejection: it is the forgery, ready to reproduce.
        VRefuted cex -> do
          emitDiagnostic opts source (refutationDiagnostic modulus cex)
          exitFailure

        -- Honest incompleteness.
        VUnknown residual -> do
          emitDiagnostic opts source (residualDiagnostic residual)
          exitFailure

-- | @zkc doc@ — generate the gadget reference from determinacy summaries.
-- Resolves includes and elaborates exactly as @build@ does, then, instead of
-- proving the circuit and emitting IR, proves each gadget and renders its
-- summary. (Phase 6, M.2)
runDoc :: Options -> IO ()
runDoc opts = do
  source <- readFileUtf8 (optInput opts)
  case parseProgram source of
    Left problem -> emitDiagnostic opts source problem >> exitFailure
    Right program0 -> do
      resolved <- resolveUses opts program0
      case resolved of
        Left problem -> emitDiagnostic opts source problem >> exitFailure
        Right program -> case elaborate (optField opts) program of
          Left problem -> emitDiagnostic opts source problem >> exitFailure
          Right elab -> case fieldModulus (optField opts) of
            Nothing -> emitDiagnostic opts source
              (diag ("unknown field '" ++ optField opts ++ "'")) >> exitFailure
            Just modulus ->
              case gadgetSummaries modulus (elabGadgetBodies elab) of
                Left failure ->
                  emitDiagnostic opts source (determinacyDiagnostic failure) >> exitFailure
                Right summaries -> do
                  let doc = renderReference summaries
                  case optOutput opts of
                    Nothing   -> putStr doc
                    Just path -> writeFileUtf8 path doc
                  exitSuccess

-- | Parse, resolve @use@ includes (IO), then elaborate. The only IO at the
-- front of the pipeline, because resolving an include reads a file.
prepareIO :: Options -> String -> IO (Either Diagnostic (Elaborated, Integer))
prepareIO opts source =
  case parseProgram source of
    Left problem -> pure (Left problem)
    Right program0 -> do
      resolved <- resolveUses opts program0
      pure (resolved >>= elaborateStep opts)

-- | Elaboration and modulus lookup — everything up to (but not including) the
-- determinacy proof, over an already-parsed, already-resolved program.
elaborateStep :: Options -> Program -> Either Diagnostic (Elaborated, Integer)
elaborateStep opts program = do
  elab <- elaborate (optField opts) program
  modulus <- case fieldModulus (optField opts) of
    Just p -> Right p
    Nothing -> Left $ withHelp ("known fields: " ++ unwords (map fst knownFields))
      $ diag ("unknown field '" ++ optField opts ++ "'; the determinacy analysis \
              \needs its modulus to decide whether a coefficient is nonzero")
  Right (elab, modulus)

-- | Resolve @use module::item;@ includes: read each library file, parse its
-- gadget definitions, and merge them into the program (dedup by name; the
-- program's own gadgets win a clash). The @std@ module resolves to the
-- directory named by $ZKC_STD_PATH, or ./std by default. (Phase 6, M.2)
resolveUses :: Options -> Program -> IO (Either Diagnostic Program)
resolveUses _opts program = do
  stdDir <- maybe "std" id <$> lookupEnv "ZKC_STD_PATH"
  go stdDir (progUses program) []
  where
    go _ [] acc =
      pure (Right (program { progGadgets = dedupBy gdName (progGadgets program ++ acc) }))
    go stdDir (u : us) acc = do
      let dir  = if udModule u == "std" then stdDir else udModule u
          path = dir ++ "/" ++ udItem u ++ ".zkc"
      result <- tryIOError (readFileUtf8 path)
      case result of
        Left _ -> pure (Left (useUnreadable u path))
        Right src -> case parseGadgets src of
          Left d -> pure (Left d)
          Right gs
            | any ((== udItem u) . gdName) gs -> go stdDir us (acc ++ gs)
            | otherwise -> pure (Left (useMissingGadget u path))

    dedupBy key xs = reverse (foldl step [] xs)
      where step acc x | any ((== key x) . key) acc = acc
                       | otherwise = x : acc

    useUnreadable u path = diagAt (udLine u) $
      "cannot resolve 'use " ++ udModule u ++ "::" ++ udItem u
      ++ "': could not read '" ++ path ++ "'"
    useMissingGadget u path = diagAt (udLine u) $
      "library '" ++ path ++ "' does not define a gadget named '" ++ udItem u ++ "'"

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
  , "  zkc lsp              run the language server (LSP over stdin/stdout)"
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