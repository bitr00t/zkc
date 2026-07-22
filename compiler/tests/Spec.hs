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
import Zkc.Analysis.Smt
  ( Dialect(..), Query(..), SolverAnswer(..), buildQuery, parseAnswer )
import Zkc.Core.Elaborate (elaborate, Elaborated(..))
import Zkc.Core.Ir
import Zkc.Core.Passes (optimize, Stats(..))
import Zkc.Diagnostics
import Zkc.Emit.Json (emitJson)
import Zkc.Field (fieldModulus)
import Zkc.Syntax.Ast
import Zkc.Syntax.Lexer (lexer, Tok(..), Token(..))
import Zkc.Syntax.Parser (parseProgram, parseCircuit)

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

elab :: String -> Either Diagnostic Elaborated
elab source = parseProgram source >>= elaborate "bn254"

-- | The flat, backend-facing IR.
compileIr :: String -> Either Diagnostic Ir
compileIr source = elabIr <$> elab source

-- | Compile and optimize, as the CLI does by default.
compileOpt :: String -> Either Diagnostic (Ir, Stats)
compileOpt source = optimize <$> compileIr source

-- | Determinacy the phase-2 way: monolithically, on the fully inlined IR.
-- Still valid, and what the optimiser-equivalence check leans on.
determinacyOf :: String -> Either Diagnostic (Either Failure Report)
determinacyOf source = do
  (ir, _) <- compileOpt source
  pure (checkDeterminacy bn254 ir)

-- | Determinacy the phase-3 way: compositionally, proving each gadget once
-- and reusing the summary at every call site.
checkProgramOf :: String -> Either Diagnostic (Either Failure Report)
checkProgramOf source = do
  e <- elab source
  pure (either (Left . pfFailure) Right
          (checkProgram bn254 (elabGadgetBodies e) (elabCircuitBody e)))

-- | The failing scope, for tests about /where/ an obligation stayed open.
scopeOfFailure :: String -> Maybe (String, Bool)
scopeOfFailure source = case elab source of
  Right e -> case checkProgram bn254 (elabGadgetBodies e) (elabCircuitBody e) of
    Left problem -> Just (pfScope problem, pfIsGadget problem)
    Right _ -> Nothing
  Left _ -> Nothing

-- Helpers for the SMT layer ---------------------------------------------

circuitBodyOf :: String -> Maybe Body
circuitBodyOf source = either (const Nothing) (Just . elabCircuitBody) (elab source)

gadgetBodyOf :: String -> String -> Maybe Body
gadgetBodyOf source name = case elab source of
  Right e -> lookup name [ (gdName d, b) | (d, b) <- elabGadgetBodies e ]
  Left _ -> Nothing

systemFor :: Body -> Maybe BodySystem
systemFor body = either (const Nothing) Just (bodySystem bn254 body)

-- | The SMT-LIB2 text for a scope, in the given dialect.
queryFor :: Dialect -> String -> Body -> Maybe String
queryFor dialect scope body = (qText . buildQuery bn254 dialect scope) <$> systemFor body

-- | Count non-overlapping occurrences of a needle.
occurrences :: String -> String -> Int
occurrences needle haystack =
  length [ () | suffix <- tails' haystack, needle `isPrefixOf'` suffix ]
  where
    tails' [] = [[]]
    tails' s@(_ : rest) = s : tails' rest
    isPrefixOf' p s = take (length p) s == p

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

proved :: Either Diagnostic (Either Failure Report) -> Bool
proved (Right (Right _)) = True
proved _ = False

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

-- | IsZero, now a parameterised definition. @out@ is a bare atom the body
-- only constrains, so the circuit binds it to a declared output.
isZero :: String
isZero = unlines
  [ "gadget is_zero(x: field) -> (out: field) {"
  , "    advice inv = inv_or_zero(x);"
  , "    assert x * inv == 1 - out;"
  , "    assert x * out == 0;"
  , "}"
  , "circuit IsZero {"
  , "    private x: field;"
  , "    output out: field;"
  , "    (out) = is_zero(x);"
  , "}"
  ]

isZeroBroken :: String
isZeroBroken = unlines
  [ "gadget is_zero(x: field) -> (out: field) {"
  , "    advice inv = inv_or_zero(x);"
  , "    assert x * inv == 1 - out;"
  , "}"
  , "circuit IsZeroBroken {"
  , "    private x: field;"
  , "    output out: field;"
  , "    (out) = is_zero(x);"
  , "}"
  ]

-- | Divide, exercising the other call form: @inv_b@ is a computed result
-- (produced by advice), bound freshly with @let@.
divide :: String
divide = unlines
  [ "gadget reciprocal(b: field) -> (inv_b: field) {"
  , "    advice inv_b = inv(b);"
  , "    assert b * inv_b == 1;"
  , "}"
  , "circuit Divide {"
  , "    private a: field;"
  , "    private b: field;"
  , "    output q: field;"
  , "    let (inv_b) = reciprocal(b);"
  , "    assert q == a * inv_b;"
  , "}"
  ]

-- | Four independent IsZero instances. Each needs its own x==0\/x!=0 split, so
-- proving all four at once exceeds the depth bound — but proving the gadget
-- once and reusing it does not. The compositional scaling story, in miniature.
manyIsZero :: String
manyIsZero = unlines
  [ "gadget is_zero(x: field) -> (out: field) {"
  , "    advice inv = inv_or_zero(x);"
  , "    assert x * inv == 1 - out;"
  , "    assert x * out == 0;"
  , "}"
  , "circuit Many {"
  , "    private x1: field;"
  , "    private x2: field;"
  , "    private x3: field;"
  , "    private x4: field;"
  , "    output o1: field;"
  , "    output o2: field;"
  , "    output o3: field;"
  , "    output o4: field;"
  , "    (o1) = is_zero(x1);"
  , "    (o2) = is_zero(x2);"
  , "    (o3) = is_zero(x3);"
  , "    (o4) = is_zero(x4);"
  , "}"
  ]

-- | @scale@ can only be proved with its precondition: y = v\/x is determined
-- only when x is known nonzero. @nz_source@ establishes exactly that fact, so
-- a caller that runs it first can discharge the requirement.
requireOk :: String
requireOk = unlines
  [ "gadget nz_source(b: field) -> (r: field) {"
  , "    advice r = inv(b);"
  , "    assert b * r == 1;"
  , "}"
  , "gadget scale(x: field, v: field) -> (y: field) {"
  , "    require x != 0;"
  , "    assert x * y == v;"
  , "}"
  , "circuit UsesScale {"
  , "    private b: field;"
  , "    private v: field;"
  , "    output y: field;"
  , "    let (bi) = nz_source(b);"
  , "    (y) = scale(b, v);"
  , "}"
  ]

-- | The same, but nothing establishes that b is nonzero, so @scale@'s
-- precondition cannot be discharged.
requireBad :: String
requireBad = unlines
  [ "gadget scale(x: field, v: field) -> (y: field) {"
  , "    require x != 0;"
  , "    assert x * y == v;"
  , "}"
  , "circuit UsesScale {"
  , "    private b: field;"
  , "    private v: field;"
  , "    output y: field;"
  , "    (y) = scale(b, v);"
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

  , ( "lexer: 'gadget' and 'output' are keywords"
    , case lexer "gadget output" of
        Right ts -> map tokKind ts == [TGadget, TOutput, TEof]
        Left _ -> False )

  , ( "lexer: 'require' and '!=' are lexed for preconditions"
    , case lexer "require b != 0" of
        Right ts -> map tokKind ts == [TRequire, TIdent "b", TNe, TNumber 0, TEof]
        Left _ -> False )

  , ( "lexer: '==' is one token, not two '='"
    , case lexer "a == b" of
        Right ts -> TEqEq `elem` map tokKind ts
        Left _ -> False )

  , ( "lexer: '!=' is one token, distinct from '='"
    , case lexer "a != b = c" of
        Right ts -> TNe `elem` map tokKind ts && TEq `elem` map tokKind ts
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

  , ( "parser: a gadget definition carries its params and results"
    , case parseProgram isZero of
        Right p -> case progGadgets p of
          [g] -> gdName g == "is_zero" && gdParams g == ["x"] && gdResults g == ["out"]
          _ -> False
        Left _ -> False )

  , ( "parser: the circuit body instantiates the gadget"
    , case parseProgram isZero of
        Right p -> case circBody (progCircuit p) of
          [SInstance (BindExisting ["out"]) "is_zero" [EVar "x" _] _] -> True
          _ -> False
        Left _ -> False )

  , ( "parser: 'let (r) = g(..)' is a fresh-result instance, not a scalar let"
    , case parseProgram divide of
        Right p -> case [ s | s@SInstance{} <- circBody (progCircuit p) ] of
          (SInstance (BindFresh ["inv_b"]) "reciprocal" _ _ : _) -> True
          _ -> False
        Left _ -> False )

  , ( "parser: 'require' is parsed at the head of a gadget body"
    , case parseProgram requireBad of
        Right p -> case [ g | g <- progGadgets p, gdName g == "scale" ] of
          (g:_) -> map rqName (gdRequires g) == ["x"]
          _ -> False
        Left _ -> False )

  , ( "parser: '*' binds tighter than '+'"
    , case parseCircuit "circuit C { output z: field; assert z == 1 + 2 * 3; }" of
        Right (Circuit _ _ [SAssert _ (EAdd _ (EMul _ _ _) _) _]) -> True
        _ -> False )

  , ( "parser: missing semicolon names the expected token and line"
    , failsWith "expected ';'" (parseCircuit "circuit C { output z: field; assert z == 1 }") )

  , ( "parser: advice may only be bound to a hint call"
    , failsWith "must be a hint call"
        (parseProgram "circuit C { private x: field; advice w = x * x; }") )

  , ( "parser: an unknown hint is rejected by name"
    , failsWith "'sqrt' is not a known hint"
        (parseProgram "circuit C { private x: field; advice w = sqrt(x); }") )

  , ( "parser: a file needs exactly one circuit"
    , failsWith "exactly one 'circuit'"
        (parseProgram "gadget g(x: field) -> (y: field) { assert y == x; }") )

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

  -- Gadget quarantine and scoping ---------------------------------------
  , ( "quarantine: advice outside a gadget is rejected"
    , failsWith "may only appear inside a 'gadget'"
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

  , ( "quarantine: gadgets are top-level and do not nest"
    , failsWith "found 'gadget'"
        (parseProgram "gadget a(x: field) -> (y: field) { gadget b(z: field) -> (w: field) { } }") )

  , ( "scoping: a gadget's internal bindings do not leak into the circuit"
    , failsWith "'tmp' is not defined"
        (compileIr (unlines
          [ "gadget g(x: field) -> (y: field) { let tmp = x + x; assert y == tmp; }"
          , "circuit C { private x: field; output y: field;"
          , "            (y) = g(x); assert x == tmp; }" ])) )

  , ( "scoping: each instantiation gets fresh wires (no sharing)"
    , case compileIr manyIsZero of
        Right ir -> length (adviceWires ir) == 4
        Left _ -> False )

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
        (compileIr (unlines
          [ "gadget g(x: field) -> (o: field) {"
          , "    advice ghost = inv_or_zero(x); assert o == x * x; }"
          , "circuit C { private x: field; output o: field; (o) = g(x); }" ])) )

  , ( "elaborate: an unknown gadget is reported"
    , failsWith "unknown gadget 'missing'"
        (compileIr "circuit C { private x: field; output o: field; (o) = missing(x); }") )

  , ( "elaborate: an arity mismatch is reported"
    , failsWith "expects 1 argument"
        (compileIr (unlines
          [ "gadget g(x: field) -> (y: field) { assert y == x; }"
          , "circuit C { private a: field; private b: field; output o: field;"
          , "            (o) = g(a, b); }" ])) )

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

  -- Determinacy: monolithic proofs on the inlined IR --------------------
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

  -- Determinacy: compositional proofs -----------------------------------
  , ( "compositional: IsZero proved by summary, x==0 / x!=0 surfaced from the gadget"
    , case checkProgramOf isZero of
        Right (Right report) ->
          repTargets report == [2]
          && length (repAssumptions report) == 2
          && any (any isZeroAssumption) (repAssumptions report)
          && any (any isNonZeroAssumption) (repAssumptions report)
        _ -> False )

  , ( "compositional: Divide proved by summary, with b's branches remapped to the caller"
    , provedWith 2 (checkProgramOf divide) )

  , ( "compositional: four IsZero instances are proved by reusing one summary"
    , proved (checkProgramOf manyIsZero) )

  , ( "compositional: the SAME four-instance circuit exceeds the depth bound monolithically"
    , case determinacyOf manyIsZero of
        Right (Left _) -> True   -- inlined-and-monolithic gives up: 4 splits > depth 3
        _ -> False )

  , ( "compositional: per-gadget branches concatenate (2N), they do not explode (2^N)"
    , case checkProgramOf manyIsZero of
        Right (Right report) -> length (repAssumptions report) == 8
        _ -> False )

  -- Preconditions -------------------------------------------------------
  , ( "require: 'scale' is proved only because 'x != 0' is assumed in its body"
    , proved (checkProgramOf requireOk) )

  , ( "require: the precondition is discharged by a prior nonzero guarantee"
    , case checkProgramOf requireOk of
        Right (Right report) -> repTargets report == [3]  -- output y
        _ -> False )

  , ( "require: an undischarged precondition is a compile-time failure"
    , case checkProgramOf requireBad of
        Right (Left failure) -> "requires its argument to be nonzero" `isInfixOf`
                                  maybe "" id (failNote failure)
        _ -> False )

  -- Determinacy: circuits that must be REJECTED --------------------------
  , ( "determinacy: THE CRITERION — under-constrained IsZero is rejected"
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
        [ "gadget g(x: field) -> (out: field) {"
        , "    advice inv = inv_or_zero(x);"
        , "    assert x * out == 0;"
        , "    assert inv * x == inv * x;"
        , "}"
        , "circuit C { private x: field; output out: field; (out) = g(x); }" ])) /= Nothing )

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

  -- SMT escalation: the query, built without ever running a solver -----
  , ( "smt: the failing scope is named, so escalation asks about it alone"
    , scopeOfFailure isZeroBroken == Just ("is_zero", True) )

  , ( "smt: the system carries one equation per assertion, over named atoms"
    , case gadgetBodyOf isZero "is_zero" >>= systemFor of
        Just system ->
          length (bsEquations system) == 2
          && map snd (bsAtoms system) == ["x", "out", "inv"]
          && [ n | (_, n, _) <- bsTargets system ] == ["out"]
          && bsInputs system == [1]
        Nothing -> False )

  , ( "smt: the query declares both witness copies of every atom"
    , case gadgetBodyOf isZero "is_zero" >>= queryFor IntegerMod "is_zero" of
        -- three atoms (x, out, inv), twice over
        Just text -> occurrences "(declare-fun " text == 6
        Nothing -> False )

  , ( "smt: the copies are forced to agree on the inputs"
    , case gadgetBodyOf isZero "is_zero" >>= queryFor IntegerMod "is_zero" of
        Just text -> "(assert (= w1_1 w1_2))" `isInfixOf` text
        Nothing -> False )

  , ( "smt: the question asked is whether an output can still differ"
    , case gadgetBodyOf isZero "is_zero" >>= queryFor IntegerMod "is_zero" of
        Just text -> "(assert (not (= (mod w2_1 P) (mod w2_2 P))))" `isInfixOf` text
        Nothing -> False )

  , ( "smt: the ff dialect speaks QF_FF and field operations natively"
    , case gadgetBodyOf isZero "is_zero" >>= queryFor FiniteField "is_zero" of
        Just text -> "(set-logic QF_FF)" `isInfixOf` text
                     && "FiniteField" `isInfixOf` text
                     && "ff.mul" `isInfixOf` text
                     -- no modular encoding anywhere: the field is native here
                     && not ("(mod " `isInfixOf` text)
        Nothing -> False )

  , ( "smt: the int dialect encodes the field as bounded integers with mod"
    , case gadgetBodyOf isZero "is_zero" >>= queryFor IntegerMod "is_zero" of
        Just text -> "(set-logic QF_NIA)" `isInfixOf` text
                     && "(mod " `isInfixOf` text
                     && "(>= w1_1 0)" `isInfixOf` text
        Nothing -> False )

  , ( "smt: a gadget's precondition is assumed in both copies, not refuted"
    , case gadgetBodyOf requireOk "scale" >>= queryFor IntegerMod "scale" of
        Just text -> occurrences "(assert (not (= (mod w1_" text == 2
        Nothing -> False )

  -- The soundness asymmetry: relaxations may prove, but must not refute --
  , ( "smt: a scope that instantiates gadgets is flagged as a relaxation"
    , case circuitBodyOf isZero >>= systemFor of
        Just system -> not (bsSelfContained system)
        Nothing -> False )

  , ( "smt: a gadget body with no instances is self-contained"
    , case gadgetBodyOf isZero "is_zero" >>= systemFor of
        Just system -> bsSelfContained system
        Nothing -> False )

  -- Reading the solver back ---------------------------------------------
  , ( "smt: unsat is read as proved"
    , parseAnswer "unsat\n" == AnswerUnsat )

  , ( "smt: sat is read together with its model"
    , parseAnswer "sat\n((w1_1 2) (w2_1 1))" == AnswerSat [("w1_1", 2), ("w2_1", 1)] )

  , ( "smt: a solver that gives up is not mistaken for an answer"
    , case parseAnswer "unknown" of
        AnswerUnknown _ -> True
        _ -> False )

  , ( "smt: a timeout is reported as a timeout, never as a refutation"
    , case parseAnswer "timeout" of
        AnswerUnknown reason -> "timed out" `isInfixOf` reason
        _ -> False )

  , ( "smt: an error from the solver is not silently read as a verdict"
    , case parseAnswer "(error \"not configured with --cocoa\")" of
        AnswerUnknown reason -> "unrecognised" `isInfixOf` reason
        _ -> False )

  , ( "smt: negative and field-literal model values are understood"
    , parseAnswer "sat\n((a (- 5)) (b #f7m11) (c (as ff9 F)))"
        == AnswerSat [("a", -5), ("b", 7), ("c", 9)] )

  -- Golden IR: the rewrite is behaviour-preserving ----------------------
  , ( "golden: rewritten IsZero inlines to the same shape (2 inputs, 6 nodes, 2 assertions)"
    , case compileIr isZero of
        Right ir -> length (irInputs ir) == 2
                    && length (irNodes ir) == 6
                    && length (irAssertions ir) == 2
        Left _ -> False )

  , ( "golden: rewritten Divide inlines to the same shape (3 inputs, 4 nodes, 2 assertions)"
    , case compileIr divide of
        Right ir -> length (irInputs ir) == 3
                    && length (irNodes ir) == 4
                    && length (irAssertions ir) == 2
        Left _ -> False )
  ]