-- | Test suite for the compiler frontend.
--
-- A hand-rolled harness rather than HUnit\/tasty, for the same reason the
-- compiler has no dependencies: @make test@ must work with nothing but GHC.
module Main (main) where

import Data.List (isInfixOf)
import qualified Data.Set as Set
import System.Exit (exitFailure, exitSuccess)
import System.IO (hSetEncoding, stdout, utf8)

import Zkc.Analysis.Determinacy
import qualified Zkc.Analysis.Poly as P
import Zkc.Core.Elaborate (elaborate)
import Zkc.Core.Ir
import Zkc.Core.Passes (optimize, Stats(..))
import Zkc.Diagnostics
import Zkc.Emit.Json (emitJson)
import Zkc.Field (fieldModulus)
import Zkc.Syntax.Ast
import Zkc.Syntax.Lexer (lexer, Tok(..), Token(..))
import Zkc.Syntax.Parser (parseCircuit)

main :: IO ()
main = do
  hSetEncoding stdout utf8
  results <- mapM runCase cases
  let failures = length (filter not results)
  putStrLn $ "\n" ++ show (length cases - failures) ++ "/" ++ show (length cases)
             ++ " checks passed"
  if failures == 0 then exitSuccess else exitFailure

runCase :: (String, Bool) -> IO Bool
runCase (name, ok) = do
  putStrLn $ (if ok then "  ok:   " else "  FAIL: ") ++ name
  pure ok

-- Helpers ---------------------------------------------------------------

bn254 :: Integer
bn254 = maybe (error "bn254 must be a known field") id (fieldModulus "bn254")

compileIr :: String -> Either Diagnostic Ir
compileIr source = parseCircuit source >>= elaborate "bn254"

-- | Compile and optimize, as the CLI does by default.
compileOpt :: String -> Either Diagnostic (Ir, Stats)
compileOpt source = optimize <$> compileIr source

-- | The full frontend, ending in the determinacy proof.
determinacyOf :: String -> Either Diagnostic (Either Failure Report)
determinacyOf source = do
  (ir, _) <- compileOpt source
  pure (checkDeterminacy bn254 ir)

-- | True when compilation fails with a diagnostic mentioning the needle
-- anywhere: message, notes or suggestion.
failsWith :: String -> Either Diagnostic a -> Bool
failsWith needle (Left d) =
  any (needle `isInfixOf`) (diagMessage d : diagNotes d ++ maybe [] pure (diagHelp d))
failsWith _ (Right _) = False

-- | The determinacy pass proved everything, using this many branches.
provedWith :: Int -> Either Diagnostic (Either Failure Report) -> Bool
provedWith branches (Right (Right report)) = length (repAssumptions report) == branches
provedWith _ _ = False

rejected :: Either Diagnostic (Either Failure Report) -> Maybe Failure
rejected (Right (Left failure)) = Just failure
rejected _ = Nothing

wireNamed :: String -> Ir -> WireId
wireNamed name ir = head ([ iiWire i | i <- irInputs ir, iiName i == name ] ++ [-1])

countOps :: (Op -> Bool) -> Ir -> Int
countOps predicate ir = length [ () | n <- irNodes ir, predicate (nOp n) ]

isMul :: Op -> Bool
isMul (OMul _ _) = True
isMul _ = False

isZeroAssumption :: Assumption -> Bool
isZeroAssumption (AssumeZero _) = True
isZeroAssumption _ = False

isNonZeroAssumption :: Assumption -> Bool
isNonZeroAssumption (AssumeNonZero _) = True
isNonZeroAssumption _ = False

withJson :: String -> (String -> Bool) -> Bool
withJson source predicate = case compileOpt source of
  Right (ir, _) -> case checkDeterminacy bn254 ir of
    Right report -> predicate (emitJson report ir)
    Left _ -> False
  Left _ -> False

-- Sources ---------------------------------------------------------------

mulSquare :: String
mulSquare = unlines
  [ "circuit MulSquare {"
  , "    private a: field;"
  , "    private b: field;"
  , "    output c: field;"
  , "    let ab = a * b;"
  , "    assert c == ab * ab;"
  , "}"
  ]

isZero :: String
isZero = unlines
  [ "circuit IsZero {"
  , "    private x: field;"
  , "    output out: field;"
  , "    gadget is_zero {"
  , "        advice inv = inv_or_zero(x);"
  , "        assert x * inv == 1 - out;"
  , "        assert x * out == 0;"
  , "    }"
  , "}"
  ]

isZeroBroken :: String
isZeroBroken = unlines
  [ "circuit IsZeroBroken {"
  , "    private x: field;"
  , "    output out: field;"
  , "    gadget is_zero {"
  , "        advice inv = inv_or_zero(x);"
  , "        assert x * inv == 1 - out;"
  , "    }"
  , "}"
  ]

divide :: String
divide = unlines
  [ "circuit Divide {"
  , "    private a: field;"
  , "    private b: field;"
  , "    output q: field;"
  , "    gadget reciprocal {"
  , "        advice inv_b = inv(b);"
  , "        assert b * inv_b == 1;"
  , "    }"
  , "    assert q == a * inv_b;"
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

  , ( "lexer: 'gadget' and 'output' are keywords in phase 2"
    , case lexer "gadget output" of
        Right ts -> map tokKind ts == [TGadget, TOutput, TEof]
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
    , case lexer "let\n#" of
        Left d -> diagLine d == Just 2
        Right _ -> False )

  -- Parser --------------------------------------------------------------
  , ( "parser: accepts a full circuit"
    , case parseCircuit mulSquare of
        Right c -> circName c == "MulSquare" && length (circParams c) == 3
        Left _ -> False )

  , ( "parser: 'output' is a third visibility, distinct from 'public'"
    , case parseCircuit mulSquare of
        Right c -> map pdVisibility (circParams c) == [Private, Private, Output]
        Left _ -> False )

  , ( "parser: gadget blocks nest statements"
    , case parseCircuit isZero of
        Right (Circuit _ _ [SGadget name body _]) -> name == "is_zero" && length body == 3
        _ -> False )

  , ( "parser: '*' binds tighter than '+'"
    , case parseCircuit "circuit C { output z: field; assert z == 1 + 2 * 3; }" of
        Right (Circuit _ _ [SAssert _ (EAdd _ (EMul _ _ _) _) _]) -> True
        _ -> False )

  , ( "parser: missing semicolon names the expected token and line"
    , failsWith "expected ';'" (parseCircuit "circuit C { output z: field; assert z == 1 }") )

  , ( "parser: advice may only be bound to a hint call"
    , failsWith "must be a hint call"
        (parseCircuit "circuit C { private x: field; advice w = x * x; }") )

  , ( "parser: an unknown hint is rejected by name"
    , failsWith "'sqrt' is not a known hint"
        (parseCircuit "circuit C { private x: field; advice w = sqrt(x); }") )

  -- Diagnostics ---------------------------------------------------------
  , ( "diagnostics: errors carry a line, notes and a suggestion"
    , case compileIr "circuit C { private x: field; output o: field; \
                     \advice inv = inv_or_zero(x); assert o == x * inv; }" of
        Left d -> diagLine d /= Nothing && not (null (diagNotes d)) && diagHelp d /= Nothing
        Right _ -> False )

  , ( "diagnostics: rendering echoes the offending source line"
    , let source = "circuit C {\n  private x: field;\n  bad\n}"
      in case parseCircuit source of
           Left d -> "bad" `isInfixOf` render "t.zkc" source d
           Right _ -> False )

  -- Gadget quarantine ---------------------------------------------------
  , ( "quarantine: advice outside a gadget is rejected"
    , failsWith "may only appear inside a 'gadget' block"
        (compileIr "circuit C { private x: field; output o: field; \
                   \advice inv = inv_or_zero(x); assert o == x * inv; }") )

  , ( "quarantine: the same advice inside a gadget is accepted"
    , case compileIr isZero of
        Right ir -> length (adviceWires ir) == 1
        Left _ -> False )

  , ( "quarantine: hint nodes record which gadget they came from"
    , case compileIr isZero of
        Right ir -> map (hiGadget . snd) (adviceWires ir) == ["is_zero"]
        Left _ -> False )

  , ( "quarantine: gadgets do not nest"
    , failsWith "do not nest"
        (compileIr "circuit C { private x: field; gadget a { gadget b { \
                   \advice w = inv(x); assert x * w == 1; } } }") )

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

  , ( "elaborate: advice no assertion uses is rejected as dead weight"
    , failsWith "is never used by any assertion"
        (compileIr "circuit C { private x: field; output o: field; \
                   \gadget g { advice ghost = inv_or_zero(x); } assert o == x * x; }") )

  , ( "elaborate: wire 0 is reserved and inputs start at 1"
    , case compileIr isZero of
        Right ir -> map iiWire (irInputs ir) == [1, 2] && constOneWire == 0
        Left _ -> False )

  , ( "elaborate: nodes are emitted in topological order"
    , case compileIr isZero of
        Right ir -> and [ all (< nWire n) (opArgs (nOp n)) | n <- irNodes ir ]
        Left _ -> False )

  , ( "elaborate: advice taint propagates, and untainted wires stay clean"
    , case compileIr isZero of
        Right ir ->
          let tainted = adviceDerived ir
          in all (`Set.member` tainted) (map fst (adviceWires ir))
             && not (wireNamed "x" ir `Set.member` tainted)
        Left _ -> False )

  -- Polynomials ---------------------------------------------------------
  , ( "poly: arithmetic reduces modulo the field"
    , P.asConstant (P.constant 17 20) == Just 3 )

  , ( "poly: (x + 1) * (x - 1) expands to x^2 - 1"
    , let x = P.var bn254 1
          one = P.constant bn254 1
      in P.mul bn254 (P.add bn254 x one) (P.sub bn254 x one)
         == P.sub bn254 (P.mul bn254 x x) one )

  , ( "poly: substituting zero drops every monomial mentioning the atom"
    , let expr = P.add bn254 (P.mul bn254 (P.var bn254 1) (P.var bn254 2))
                             (P.constant bn254 5)
      in P.asConstant (P.substituteZero 1 expr) == Just 5 )

  , ( "poly: splitLinear separates the coefficient from the remainder"
    , let x = P.var bn254 1
          expr = P.sub bn254 (P.mul bn254 x (P.var bn254 2)) (P.constant bn254 3)
      in case P.splitLinear bn254 2 expr of
           Just (coefficient, remainder) ->
             coefficient == x && P.asConstant remainder == Just (bn254 - 3)
           Nothing -> False )

  , ( "poly: splitLinear refuses degree 2, where a nonzero coefficient does \
      \not imply a unique root"
    , P.splitLinear bn254 2 (P.mul bn254 (P.var bn254 2) (P.var bn254 2)) == Nothing )

  , ( "poly: a monomial of nonzero atoms is nonzero (fields have no zero divisors)"
    , let expr = P.mul bn254 (P.var bn254 1) (P.var bn254 2)
      in P.isSingleMonomialIn (Set.fromList [1, 2]) expr
         && not (P.isSingleMonomialIn (Set.fromList [1]) expr) )

  -- Determinacy: circuits that must be PROVED ---------------------------
  , ( "determinacy: a purely computed output needs no case split"
    , provedWith 1 (determinacyOf mulSquare) )

  , ( "determinacy: IsZero is proved, and needs exactly the x==0 / x!=0 split"
    , case determinacyOf isZero of
        Right (Right report) ->
          length (repAssumptions report) == 2
          && any (any isZeroAssumption) (repAssumptions report)
          && any (any isNonZeroAssumption) (repAssumptions report)
        _ -> False )

  , ( "determinacy: Divide is proved, chaining through a pinned advice wire"
    , provedWith 2 (determinacyOf divide) )

  , ( "determinacy: an output fixed by a constant is determined"
    , provedWith 1 (determinacyOf "circuit C { output z: field; assert z == 7; }") )

  , ( "determinacy: outputs may depend on public inputs, not only private ones"
    , provedWith 1 (determinacyOf "circuit C { public h: field; output o: field; \
                                  \assert o == h + 1; }") )

  , ( "determinacy: a circuit with no outputs has nothing to prove"
    , case determinacyOf "circuit C { public a: field; public b: field; \
                         \assert a * b == 12; }" of
        Right (Right report) -> null (repTargets report)
        _ -> False )

  -- Determinacy: circuits that must be REJECTED --------------------------
  , ( "determinacy: THE PHASE-2 CRITERION — under-constrained IsZero is rejected"
    , case (compileOpt isZeroBroken, rejected (determinacyOf isZeroBroken)) of
        (Right (ir, _), Just failure) -> failTarget failure == wireNamed "out" ir
        _ -> False )

  , ( "determinacy: the rejection names the branch where the output stays free"
    , case rejected (determinacyOf isZeroBroken) of
        Just failure -> any isNonZeroAssumption (failAssumptions failure)
        Nothing -> False )

  , ( "determinacy: the rejection names the advice the prover may still choose"
    , case (compileOpt isZeroBroken, rejected (determinacyOf isZeroBroken)) of
        (Right (ir, _), Just failure) ->
          failFreeAdvice failure == map fst (adviceWires ir)
        _ -> False )

  , ( "determinacy: a squared output is rejected, since z^2 = 4 has two roots"
    , rejected (determinacyOf "circuit C { output z: field; assert z * z == 4; }")
      /= Nothing )

  , ( "determinacy: keeping only the second IsZero assertion is not enough either"
    , rejected (determinacyOf (unlines
        [ "circuit C {"
        , "    private x: field;"
        , "    output out: field;"
        , "    gadget g {"
        , "        advice inv = inv_or_zero(x);"
        , "        assert x * out == 0;"
        , "        assert inv * x == inv * x;"
        , "    }"
        , "}" ])) /= Nothing )

  -- Passes --------------------------------------------------------------
  , ( "passes: constant subexpressions are folded"
    , case compileOpt "circuit C { output z: field; assert z == 2 * 3 + 4; }" of
        Right (_, stats) -> statsFolded stats > 0
        Left _ -> False )

  , ( "passes: repeated subexpressions are shared (CSE)"
    , case compileOpt "circuit C { private a: field; private b: field; output z: field; \
                      \assert z == (a * b) + (a * b); }" of
        Right (ir, stats) -> statsShared stats > 0 && countOps isMul ir == 1
        Left _ -> False )

  , ( "passes: nodes no assertion depends on are dropped"
    , case compileOpt "circuit C { private a: field; private b: field; output z: field; \
                      \let dead = a * b; assert z == a; }" of
        Right (_, stats) -> statsDropped stats > 0
        Left _ -> False )

  , ( "passes: optimization preserves determinacy (same solution set)"
    , case (checkDeterminacy bn254 <$> compileIr isZero, determinacyOf isZero) of
        (Right (Right before), Right (Right after)) ->
          repTargets before == repTargets after
        _ -> False )

  , ( "passes: wires stay dense and ordered after renumbering"
    , case compileOpt isZero of
        Right (ir, _) ->
          let base = 1 + length (irInputs ir)
          in map nWire (irNodes ir) == take (length (irNodes ir)) [base ..]
        Left _ -> False )

  -- JSON ----------------------------------------------------------------
  , ( "json: announces schema version 2"
    , withJson isZero ("\"schema_version\":2" `isInfixOf`) )

  , ( "json: records the output visibility"
    , withJson isZero ("\"visibility\":\"output\"" `isInfixOf`) )

  , ( "json: hint nodes carry their gadget"
    , withJson isZero ("\"gadget\":\"is_zero\"" `isInfixOf`) )

  , ( "json: wires are tagged with the advice taint"
    , withJson isZero ("\"advice_derived\":true" `isInfixOf`) )

  , ( "json: the determinacy proof travels with the IR"
    , withJson isZero (\j -> "\"determinacy\"" `isInfixOf` j
                             && "\"proved\":true" `isInfixOf` j
                             && "x != 0" `isInfixOf` j) )

  , ( "json: constants are strings, since field elements exceed 64 bits"
    , withJson "circuit C { output z: field; assert z == 7; }"
        ("\"value\":\"7\"" `isInfixOf`) )

  , ( "json: assertion labels keep the source text for backend errors"
    , withJson isZero ("(x * out) == 0" `isInfixOf`) )
  ]