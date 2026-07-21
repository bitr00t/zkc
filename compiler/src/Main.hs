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
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.IO
  ( IOMode(ReadMode, WriteMode), hClose, hGetContents, hPutStr, hPutStrLn
  , hSetEncoding, openFile, stderr, stdout, utf8 )

import Zkc.Analysis.Determinacy
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
  }

defaultOptions :: FilePath -> Options
defaultOptions input = Options
  { optInput = input
  , optOutput = Nothing
  , optField = "bn254"
  , optOptimize = True
  , optQuiet = False
  , optExplain = False
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
parseOptions _ (flag : _) = Left ("unknown option: " ++ flag)

run :: Options -> IO ()
run opts = do
  source <- readFileUtf8 (optInput opts)
  case compile opts source of
    Left problem -> do
      hPutStr stderr (render (optInput opts) source problem)
      exitFailure
    Right (json, ir, stats, report) -> do
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
        hPutStrLn stderr ("  determinacy: " ++ summariseReport ir report)
        when (optExplain opts) (explain ir report)
      exitSuccess

compile :: Options -> String -> Either Diagnostic (String, Ir, Stats, Report)
compile opts source = do
  program <- parseProgram source
  elab <- elaborate (optField opts) program
  modulus <- case fieldModulus (optField opts) of
    Just p -> Right p
    Nothing -> Left $ withHelp ("known fields: " ++ unwords (map fst knownFields))
      $ diag ("unknown field '" ++ optField opts ++ "'; the determinacy analysis \
              \needs its modulus to decide whether a coefficient is nonzero")
  -- Determinacy runs compositionally on the pre-optimisation skeletons: each
  -- gadget is proved once, and the circuit reuses those proofs. Optimisation
  -- preserves the solution set, so a proof valid here stays valid after it.
  report <- either (Left . determinacyDiagnostic (elabIr elab)) Right
              (checkProgram modulus (elabGadgetBodies elab) (elabCircuitBody elab))
  let (ir, stats) = if optOptimize opts then optimize (elabIr elab) else (elabIr elab, Stats 0 0 0)
  Right (emitJson report ir, ir, stats, report)

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

-- | Turn a failed determinacy proof into an error a circuit author can act on.
determinacyDiagnostic :: Ir -> Failure -> Diagnostic
determinacyDiagnostic ir failure = case failNote failure of
  Just note -> withNotes [note] (diag "the determinacy analysis could not finish")
  Nothing ->
    withHelp ("add a constraint that forces '" ++ target
              ++ "' in this case, then recompile")
    $ withNotes (assumptionNote ++ adviceNote ++ [conclusion])
    $ diagAt line ("output '" ++ target ++ "' is not determined by the circuit's inputs")
  where
    target = nameOf ir (failTarget failure)
    line = case [ iiLine i | i <- irInputs ir, iiWire i == failTarget failure ] of
      (l : _) -> l
      [] -> 1

    assumptionNote = case failAssumptions failure of
      [] -> ["the constraints admit more than one value of '" ++ target
             ++ "' for the same inputs"]
      assumptions ->
        [ "under the assumption " ++ intercalate " and " (map (renderAssumption ir) assumptions)
          ++ ", the constraints admit more than one value of '" ++ target ++ "'" ]

    adviceNote = case failFreeAdvice failure of
      [] -> []
      wires ->
        [ "the prover also chooses the advice "
          ++ (if length wires == 1 then "value " else "values ")
          ++ unwords [ "'" ++ nameOf ir w ++ "'" | w <- wires ] ++ " freely" ]

    conclusion =
      "so two witnesses can agree on every input and still disagree on '"
      ++ target ++ "' — the prover picks which one to prove"

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
  , ""
  , "  --explain   print the case splits the determinacy proof used"
  , ""
  , "Emits the Core IR as JSON. Feed it to the Rust backend to lower, solve,"
  , "prove and verify."
  ]