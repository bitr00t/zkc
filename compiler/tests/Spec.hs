-- | Test suite for the compiler frontend.
--
-- A hand-rolled harness rather than HUnit\/tasty, for the same reason the
-- compiler has no dependencies: @make test@ must work with nothing but GHC.
module Main (main) where

import Data.List (isInfixOf)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hSetEncoding, stdout, utf8)

import Zkc.Core.Elaborate (elaborate)
import Zkc.Core.Ir
import Zkc.Core.Passes (optimize, Stats(..))
import Zkc.Emit.Json (emitJson)
import Zkc.Syntax.Ast
import Zkc.Syntax.Lexer (lexer, Tok(..), Token(..))
import Zkc.Syntax.Parser (parseCircuit)

main :: IO ()
main = do
  hSetEncoding stdout utf8
  results <- mapM runCase cases
  let failures = length (filter not results)
  putStrLn $ "\n" ++ show (length cases - failures) ++ "/" ++ show (length cases) ++ " checks passed"
  if failures == 0 then exitSuccess else exitFailure

runCase :: (String, Bool) -> IO Bool
runCase (name, ok) = do
  putStrLn $ (if ok then "  ok:   " else "  FAIL: ") ++ name
  pure ok

-- Helpers ---------------------------------------------------------------

compileIr :: String -> Either String Ir
compileIr source = parseCircuit source >>= elaborate "bn254"

-- | Compile and optimize, as the CLI does by default.
compileOpt :: String -> Either String (Ir, Stats)
compileOpt source = optimize <$> compileIr source

failsWith :: String -> Either String a -> Bool
failsWith needle (Left message) = needle `isInfixOf` message
failsWith _ (Right _) = False

countOps :: (Op -> Bool) -> Ir -> Int
countOps predicate ir = length [ () | n <- irNodes ir, predicate (nOp n) ]

isMul :: Op -> Bool
isMul (OMul _ _) = True
isMul _ = False

-- Sources ---------------------------------------------------------------

mulSquare :: String
mulSquare = unlines
  [ "circuit MulSquare {"
  , "    private a: field;"
  , "    private b: field;"
  , "    public c: field;"
  , "    let ab = a * b;"
  , "    assert c == ab * ab;"
  , "}"
  ]

isZero :: String
isZero = unlines
  [ "circuit IsZero {"
  , "    private x: field;"
  , "    public out: field;"
  , "    advice inv = inv_or_zero(x);"
  , "    assert x * inv == 1 - out;"
  , "    assert x * out == 0;"
  , "}"
  ]

isZeroBroken :: String
isZeroBroken = unlines
  [ "circuit IsZeroBroken {"
  , "    private x: field;"
  , "    public out: field;"
  , "    advice inv = inv_or_zero(x);"
  , "    assert x * inv == 1 - out;"
  , "}"
  ]

-- Cases -----------------------------------------------------------------

cases :: [(String, Bool)]
cases =
  -- Lexer ---------------------------------------------------------------
  [ ( "lexer: keywords and identifiers are distinguished"
    , case lexer "circuit Foo let x" of
        Right ts -> map tokKind ts == [TCircuit, TIdent "Foo", TLet, TIdent "x", TEof]
        Left _ -> False )

  , ( "lexer: '==' is one token, not two '='"
    , case lexer "a == b" of
        Right ts -> TEqEq `elem` map tokKind ts
        Left _ -> False )

  , ( "lexer: line comments are skipped and lines still counted"
    , case lexer "// note\nlet" of
        Right (t:_) -> tokKind t == TLet && tokLine t == 2
        _ -> False )

  , ( "lexer: unknown character reports its line"
    , failsWith "line 2" (lexer "let\n#") )

  -- Parser --------------------------------------------------------------
  , ( "parser: accepts a full circuit"
    , case parseCircuit mulSquare of
        Right c -> circName c == "MulSquare" && length (circParams c) == 3
        Left _ -> False )

  , ( "parser: '*' binds tighter than '+'"
    , case parseCircuit "circuit C { public z: field; assert z == 1 + 2 * 3; }" of
        Right (Circuit _ _ [SAssert _ (EAdd _ (EMul _ _ _) _) _]) -> True
        _ -> False )

  , ( "parser: missing semicolon names the expected token and line"
    , failsWith "expected ';'" (parseCircuit "circuit C { public z: field; assert z == 1 }") )

  , ( "parser: advice may only be bound to a hint call"
    , failsWith "must be a hint call"
        (parseCircuit "circuit C { private x: field; advice w = x * x; }") )

  , ( "parser: an unknown hint is rejected by name"
    , failsWith "'sqrt' is not a known hint"
        (parseCircuit "circuit C { private x: field; advice w = sqrt(x); }") )

  -- Elaboration ---------------------------------------------------------
  , ( "elaborate: undefined variable is reported with its line"
    , failsWith "'y' is not defined"
        (compileIr "circuit C { private x: field; assert x == y; }") )

  , ( "elaborate: rebinding a name is rejected"
    , failsWith "already bound"
        (compileIr "circuit C { private x: field; let a = x; let a = x; assert a == x; }") )

  , ( "elaborate: duplicate parameters are rejected"
    , failsWith "duplicate parameter"
        (compileIr "circuit C { private x: field; private x: field; assert x == x; }") )

  , ( "elaborate: wire 0 is reserved and inputs start at 1"
    , case compileIr isZero of
        Right ir -> map iiWire (irInputs ir) == [1, 2] && constOneWire == 0
        Left _ -> False )

  , ( "elaborate: a hint becomes an OHint node carrying its source name"
    , case compileIr isZero of
        Right ir -> [ name | Node _ (OHint _ name _) <- irNodes ir ] == ["inv"]
        Left _ -> False )

  , ( "elaborate: nodes are emitted in topological order"
    , case compileIr isZero of
        Right ir -> and [ all (< nWire n) (opArgs (nOp n)) | n <- irNodes ir ]
        Left _ -> False )

  -- The phase-1 determinacy approximation, and its documented limit -------
  , ( "elaborate: advice that no assertion mentions is rejected"
    , failsWith "unconstrained advice"
        (compileIr "circuit C { private x: field; public o: field; \
                   \advice g = inv_or_zero(x); assert o == x * x; }") )

  , ( "elaborate: the KNOWN GAP — under-constrained IsZero still compiles"
    , case compileIr isZeroBroken of
        Right _ -> True     -- phase 2's job to reject this
        Left _ -> False )

  -- Passes --------------------------------------------------------------
  , ( "passes: constant subexpressions are folded"
    , case compileOpt "circuit C { public z: field; assert z == 2 * 3 + 4; }" of
        Right (_, stats) -> statsFolded stats > 0
        Left _ -> False )

  , ( "passes: repeated subexpressions are shared (CSE)"
    , case compileOpt "circuit C { private a: field; private b: field; public z: field; \
                      \assert z == (a * b) + (a * b); }" of
        Right (ir, stats) -> statsShared stats > 0 && countOps isMul ir == 1
        Left _ -> False )

  , ( "passes: hints are never shared, since each is a separate free choice"
    , case compileOpt "circuit C { private x: field; public z: field; \
                      \advice p = inv_or_zero(x); advice q = inv_or_zero(x); \
                      \assert p == q; assert z == x * p; }" of
        Right (ir, _) -> length [ () | Node _ (OHint _ _ _) <- irNodes ir ] == 2
        Left _ -> False )

  , ( "passes: nodes no assertion depends on are dropped"
    , case compileOpt "circuit C { private a: field; private b: field; public z: field; \
                      \let dead = a * b; assert z == a; }" of
        Right (_, stats) -> statsDropped stats > 0
        Left _ -> False )

  , ( "passes: optimization preserves the assertion count"
    , case (compileIr isZero, compileOpt isZero) of
        (Right before, Right (after, _)) ->
          length (irAssertions before) == length (irAssertions after)
        _ -> False )

  , ( "passes: wires stay dense and ordered after renumbering"
    , case compileOpt isZero of
        Right (ir, _) ->
          let base = 1 + length (irInputs ir)
          in map nWire (irNodes ir) == take (length (irNodes ir)) [base ..]
        Left _ -> False )

  -- JSON ----------------------------------------------------------------
  , ( "json: carries the schema version and field name"
    , case compileIr isZero of
        Right ir -> let j = emitJson ir
                    in "\"schema_version\":1" `isInfixOf` j && "\"field\":\"bn254\"" `isInfixOf` j
        Left _ -> False )

  , ( "json: constants are strings, since field elements exceed 64 bits"
    , case compileIr "circuit C { public z: field; assert z == 7; }" of
        Right ir -> "\"value\":\"7\"" `isInfixOf` emitJson ir
        Left _ -> False )

  , ( "json: assertion labels keep the source text for backend errors"
    , case compileIr isZero of
        Right ir -> "(x * out) == 0" `isInfixOf` emitJson ir
        Left _ -> False )

  , ( "json: special characters in labels are escaped"
    , not ("\"\"\"" `isInfixOf` either id emitJson (compileIr isZero)) )
  ]
