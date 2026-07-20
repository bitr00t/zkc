-- | @zkc@ — the circuit compiler CLI.
--
-- > zkc build examples/iszero.zkc -o build/iszero.ir.json
--
-- Compiles a @.zkc@ source file to the serialized Core IR that the Rust
-- backend consumes. The compiler never touches cryptography: it stops at the
-- arithmetization-agnostic IR, and the backend decides whether that becomes
-- R1CS (today) or AIR for a FRI prover (phase 5).
module Main (main) where

import Control.Monad (when)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.IO
  ( IOMode(ReadMode, WriteMode), hGetContents, hPutStr, hPutStrLn, hSetEncoding
  , openFile, hClose, stderr, stdout, utf8 )

import Zkc.Core.Elaborate (elaborate)
import Zkc.Core.Ir
import Zkc.Core.Passes (optimize, renderStats, Stats(..))
import Zkc.Emit.Json (emitJson)
import Zkc.Syntax.Parser (parseCircuit)

data Options = Options
  { optInput :: FilePath
  , optOutput :: Maybe FilePath
  , optField :: String
  , optOptimize :: Bool
  , optQuiet :: Bool
  }

defaultOptions :: FilePath -> Options
defaultOptions input = Options
  { optInput = input
  , optOutput = Nothing
  , optField = "bn254"
  , optOptimize = True
  , optQuiet = False
  }

main :: IO ()
main = do
  -- Source files are UTF-8 regardless of the user's locale; without this a
  -- comment containing a non-ASCII character would abort the compiler.
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  args <- getArgs
  case args of
    ("build" : input : rest) -> either die' run (parseOptions (defaultOptions input) rest)
    _ -> usage >> exitFailure

parseOptions :: Options -> [String] -> Either String Options
parseOptions opts [] = Right opts
parseOptions opts ("-o" : path : rest) = parseOptions opts { optOutput = Just path } rest
parseOptions opts ("--field" : name : rest) = parseOptions opts { optField = name } rest
parseOptions opts ("--no-opt" : rest) = parseOptions opts { optOptimize = False } rest
parseOptions opts ("--quiet" : rest) = parseOptions opts { optQuiet = True } rest
parseOptions _ (flag : _) = Left ("unknown option: " ++ flag)

run :: Options -> IO ()
run opts = do
  source <- readFileUtf8 (optInput opts)
  case compile opts source of
    Left message -> die' (optInput opts ++ ":" ++ message)
    Right (json, ir, stats) -> do
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
      exitSuccess

compile :: Options -> String -> Either String (String, Ir, Stats)
compile opts source = do
  circuit <- parseCircuit source
  ir0 <- elaborate (optField opts) circuit
  let (ir, stats) = if optOptimize opts
                      then optimize ir0
                      else (ir0, Stats 0 0 0)
  Right (emitJson ir, ir, stats)

-- | Read a source file as UTF-8, independent of the ambient locale.
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

die' :: String -> IO ()
die' message = hPutStrLn stderr ("error: " ++ message) >> exitFailure

usage :: IO ()
usage = mapM_ (hPutStrLn stderr)
  [ "zkc — zero-knowledge circuit compiler (phase 1)"
  , ""
  , "usage:"
  , "  zkc build <file.zkc> [-o <out.json>] [--field <name>] [--no-opt] [--quiet]"
  , ""
  , "Emits the Core IR as JSON. Feed it to the Rust backend to lower, solve,"
  , "prove and verify."
  ]