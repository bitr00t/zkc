-- | Hand-rolled JSON emitter for the Core IR — schema version 2.
--
-- The serialized IR is the Haskell/Rust boundary, so it is a real artifact:
-- versioned, specified (@ir-spec\/SCHEMA.md@) and round-tripped by tests on
-- both sides.
--
-- Version 2 adds what phase 2 learned:
--
--   * the @output@ role, distinct from @public@;
--   * @advice_derived@ on every wire — the syntactic taint;
--   * gadget provenance on hint nodes;
--   * a @determinacy@ record: which outputs were proved determined, and the
--     case splits the proof needed. A backend can refuse to prove a circuit
--     whose obligations were not discharged, which makes soundness a
--     property carried by the artifact rather than a claim about the
--     toolchain that produced it.
module Zkc.Emit.Json (emitJson) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Zkc.Analysis.Determinacy (Assumption(..), Report(..))
import Zkc.Core.Ir
import Zkc.Syntax.Ast (Visibility(..))

emitJson :: Report -> Ir -> String
emitJson report ir = object
  [ ("schema_version", number 2)
  , ("name", str (irName ir))
  , ("field", str (irField ir))
  , ("const_one_wire", number constOneWire)
  , ("inputs", array (map inputJson (irInputs ir)))
  , ("nodes", array (map (nodeJson tainted) (irNodes ir)))
  , ("assertions", array (map assertJson (irAssertions ir)))
  , ("determinacy", determinacyJson names report)
  ]
  where
    tainted = adviceDerived ir
    names = wireNames ir

-- | Wire -> source name, for rendering the proof's case splits.
wireNames :: Ir -> Map.Map WireId String
wireNames ir = Map.fromList $
  [ (iiWire i, iiName i) | i <- irInputs ir ]
  ++ [ (wire, hiName info) | (wire, info) <- adviceWires ir ]

inputJson :: IrInput -> String
inputJson i = object
  [ ("wire", number (iiWire i))
  , ("name", str (iiName i))
  , ("visibility", str (visibilityName (iiVisibility i)))
  , ("line", number (iiLine i))
  ]

visibilityName :: Visibility -> String
visibilityName v = case v of
  Private -> "private"
  Public -> "public"
  Output -> "output"

nodeJson :: Set.Set WireId -> Node -> String
nodeJson tainted (Node wire op) = object $
  ("wire", number wire)
  : ("advice_derived", bool (wire `Set.member` tainted))
  : opFields op

opFields :: Op -> [(String, String)]
opFields op = case op of
  OConst n -> [("op", str "const"), ("value", str (show n))]
  OAdd a b -> [("op", str "add"), ("args", array (map number [a, b]))]
  OSub a b -> [("op", str "sub"), ("args", array (map number [a, b]))]
  OMul a b -> [("op", str "mul"), ("args", array (map number [a, b]))]
  ONeg a   -> [("op", str "neg"), ("args", array [number a])]
  OHint info args ->
    [ ("op", str "hint")
    , ("hint", str (case hiKind info of KInvOrZero -> "inv_or_zero"; KInv -> "inv"))
    , ("name", str (hiName info))
    , ("gadget", str (hiGadget info))
    , ("line", number (hiLine info))
    , ("args", array (map number args))
    ]

assertJson :: Assertion -> String
assertJson a = object
  [ ("lhs", number (aLhs a))
  , ("rhs", number (aRhs a))
  , ("label", str (aLabel a))
  , ("line", number (aLine a))
  ]

determinacyJson :: Map.Map WireId String -> Report -> String
determinacyJson names report = object
  [ ("proved", bool True)   -- compilation fails otherwise, so reaching here means proved
  , ("targets", array [ str (nameOf w) | w <- repTargets report ])
  , ("branches", array (map branch (repAssumptions report)))
  ]
  where
    nameOf w = Map.findWithDefault ("wire" ++ show w) w names
    branch assumptions = array [ str (renderAssumption nameOf a) | a <- assumptions ]

renderAssumption :: (WireId -> String) -> Assumption -> String
renderAssumption nameOf a = case a of
  AssumeZero w -> nameOf w ++ " == 0"
  AssumeNonZero w -> nameOf w ++ " != 0"

-- Minimal JSON writers -------------------------------------------------

object :: [(String, String)] -> String
object fields = "{" ++ intercalate "," [ str k ++ ":" ++ v | (k, v) <- fields ] ++ "}"

array :: [String] -> String
array items = "[" ++ intercalate "," items ++ "]"

number :: Int -> String
number = show

bool :: Bool -> String
bool b = if b then "true" else "false"

-- | Constants are emitted as decimal *strings*: field elements routinely
-- exceed 64 bits, and JSON numbers are not safe at that width.
str :: String -> String
str s = "\"" ++ concatMap escape s ++ "\""
  where
    escape c = case c of
      '"'  -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      _    -> [c]