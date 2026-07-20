-- | Hand-rolled JSON emitter for the Core IR.
--
-- The serialized IR is the Haskell\/Rust boundary, so it is a real artifact:
-- versioned, schema'd (see @ir-spec\/SCHEMA.md@) and round-tripped by tests
-- on both sides. JSON is chosen over a binary format on purpose — for the
-- first months of a compiler, being able to read the IR in a diff is worth
-- far more than serialization speed.
--
-- Written by hand because the compiler depends on nothing outside GHC's boot
-- libraries.
module Zkc.Emit.Json (emitJson) where

import Data.List (intercalate)

import Zkc.Core.Ir
import Zkc.Syntax.Ast (Visibility(..))

emitJson :: Ir -> String
emitJson ir = object
  [ ("schema_version", number 1)
  , ("name", str (irName ir))
  , ("field", str (irField ir))
  , ("const_one_wire", number constOneWire)
  , ("inputs", array (map inputJson (irInputs ir)))
  , ("nodes", array (map nodeJson (irNodes ir)))
  , ("assertions", array (map assertJson (irAssertions ir)))
  ]

inputJson :: IrInput -> String
inputJson i = object
  [ ("wire", number (iiWire i))
  , ("name", str (iiName i))
  , ("visibility", str (case iiVisibility i of Private -> "private"; Public -> "public"))
  ]

nodeJson :: Node -> String
nodeJson (Node wire op) = object $ ("wire", number wire) : opFields op

opFields :: Op -> [(String, String)]
opFields op = case op of
  OConst n -> [("op", str "const"), ("value", str (show n))]
  OAdd a b -> [("op", str "add"), ("args", array (map number [a, b]))]
  OSub a b -> [("op", str "sub"), ("args", array (map number [a, b]))]
  OMul a b -> [("op", str "mul"), ("args", array (map number [a, b]))]
  ONeg a   -> [("op", str "neg"), ("args", array [number a])]
  OHint k name args ->
    [ ("op", str "hint")
    , ("hint", str (case k of KInvOrZero -> "inv_or_zero"; KInv -> "inv"))
    , ("name", str name)
    , ("args", array (map number args))
    ]

assertJson :: Assertion -> String
assertJson a = object
  [ ("lhs", number (aLhs a))
  , ("rhs", number (aRhs a))
  , ("label", str (aLabel a))
  , ("line", number (aLine a))
  ]

-- Minimal JSON writers -------------------------------------------------

object :: [(String, String)] -> String
object fields = "{" ++ intercalate "," [ str k ++ ":" ++ v | (k, v) <- fields ] ++ "}"

array :: [String] -> String
array items = "[" ++ intercalate "," items ++ "]"

number :: Int -> String
number = show

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