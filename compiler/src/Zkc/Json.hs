-- | A tiny, dependency-free JSON model: a value type, an encoder, and a
-- parser.
--
-- Phase 6 opens by making diagnostics machine-readable, and everything after
-- it (the language server's JSON-RPC, the profiler's report) speaks JSON too.
-- The compiler deliberately builds on nothing but GHC's boot libraries, so
-- rather than reach for @aeson@ this module supplies exactly the subset the
-- toolchain needs — objects, arrays, strings, integers, booleans and null —
-- with an encoder and a matching parser that round-trip.
--
-- It is intentionally small. Numbers are integers only (every number the
-- compiler emits is a line, a column or a count; field elements travel as
-- decimal *strings*, exactly as the IR already encodes them). The parser is
-- strict about structure but forgiving about surrounding whitespace, which is
-- all a round-trip needs.
module Zkc.Json
  ( Json(..)
  , encode
  , parse
  ) where

import Data.Char (chr, isDigit, isHexDigit, digitToInt)
import Data.List (intercalate)

-- | A JSON value. Numbers are integers, which is all the compiler emits.
data Json
  = JNull
  | JBool Bool
  | JInt Integer
  | JStr String
  | JArr [Json]
  | JObj [(String, Json)]
  deriving (Eq, Show)

-- Encoding -------------------------------------------------------------

-- | Serialise a value to a compact JSON string (no incidental whitespace, so
-- the output is stable and diff-friendly).
encode :: Json -> String
encode JNull      = "null"
encode (JBool b)  = if b then "true" else "false"
encode (JInt n)   = show n
encode (JStr s)   = encodeString s
encode (JArr xs)  = "[" ++ intercalate "," (map encode xs) ++ "]"
encode (JObj kvs) =
  "{" ++ intercalate "," [ encodeString k ++ ":" ++ encode v | (k, v) <- kvs ] ++ "}"

encodeString :: String -> String
encodeString s = "\"" ++ concatMap esc s ++ "\""
  where
    esc c = case c of
      '"'  -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      _ | c < ' '   -> "\\u" ++ pad (showHex (fromEnum c))
        | otherwise -> [c]
    pad h = replicate (4 - length h) '0' ++ h
    showHex 0 = "0"
    showHex n = go n ""
      where
        go 0 acc = acc
        go k acc = go (k `div` 16) (hexDigit (k `mod` 16) : acc)
    hexDigit d = "0123456789abcdef" !! d

-- Parsing --------------------------------------------------------------

-- | Parse a JSON string into a value, or explain why it could not.
parse :: String -> Either String Json
parse input = do
  (value, rest) <- pValue (dropWhile isJsonSpace input)
  case dropWhile isJsonSpace rest of
    [] -> Right value
    junk -> Left ("trailing characters after JSON value: " ++ take 20 junk)

isJsonSpace :: Char -> Bool
isJsonSpace c = c == ' ' || c == '\n' || c == '\r' || c == '\t'

type Parser a = String -> Either String (a, String)

pValue :: Parser Json
pValue s = case dropWhile isJsonSpace s of
  ('{' : rest) -> pObject rest
  ('[' : rest) -> pArray rest
  ('"' : rest) -> do
    (str, rest') <- pString rest
    Right (JStr str, rest')
  ('t' : 'r' : 'u' : 'e' : rest)        -> Right (JBool True, rest)
  ('f' : 'a' : 'l' : 's' : 'e' : rest)  -> Right (JBool False, rest)
  ('n' : 'u' : 'l' : 'l' : rest)        -> Right (JNull, rest)
  rest@(c : _) | c == '-' || isDigit c  -> pNumber rest
  []   -> Left "unexpected end of input, expected a JSON value"
  junk -> Left ("expected a JSON value, found: " ++ take 20 junk)

pNumber :: Parser Json
pNumber s =
  let (sign, s1) = case s of ('-' : r) -> ("-", r); _ -> ("", s)
      (digits, rest) = span isDigit s1
  in if null digits
       then Left "expected digits in a number"
       else Right (JInt (read (sign ++ digits)), rest)

-- | Parse the body of a string, already past the opening quote.
pString :: Parser String
pString = go id
  where
    go acc ('"' : rest) = Right (acc [], rest)
    go acc ('\\' : c : rest) = case c of
      '"'  -> go (acc . ('"' :)) rest
      '\\' -> go (acc . ('\\' :)) rest
      '/'  -> go (acc . ('/' :)) rest
      'n'  -> go (acc . ('\n' :)) rest
      'r'  -> go (acc . ('\r' :)) rest
      't'  -> go (acc . ('\t' :)) rest
      'b'  -> go (acc . ('\b' :)) rest
      'f'  -> go (acc . ('\f' :)) rest
      'u'  -> case rest of
        (a : b : d : e : rest')
          | all isHexDigit [a, b, d, e] ->
              let code = foldl (\n h -> n * 16 + digitToInt h) 0 [a, b, d, e]
              in go (acc . (chr code :)) rest'
        _ -> Left "malformed \\u escape in string"
      _ -> Left ("unknown escape \\" ++ [c] ++ " in string")
    go _ ('\n' : _) = Left "unescaped newline in string"
    go acc (c : rest) = go (acc . (c :)) rest
    go _ [] = Left "unterminated string"

pArray :: Parser Json
pArray s = case dropWhile isJsonSpace s of
  (']' : rest) -> Right (JArr [], rest)
  _            -> loop [] s
  where
    loop acc s' = do
      (value, s1) <- pValue s'
      case dropWhile isJsonSpace s1 of
        (',' : s2) -> loop (value : acc) s2
        (']' : s2) -> Right (JArr (reverse (value : acc)), s2)
        junk       -> Left ("expected ',' or ']' in array, found: " ++ take 20 junk)

pObject :: Parser Json
pObject s = case dropWhile isJsonSpace s of
  ('}' : rest) -> Right (JObj [], rest)
  _            -> loop [] s
  where
    loop acc s' = do
      (key, s1) <- case dropWhile isJsonSpace s' of
        ('"' : r) -> pString r
        junk      -> Left ("expected a string key in object, found: " ++ take 20 junk)
      s2 <- case dropWhile isJsonSpace s1 of
        (':' : r) -> Right r
        junk      -> Left ("expected ':' after object key, found: " ++ take 20 junk)
      (value, s3) <- pValue s2
      case dropWhile isJsonSpace s3 of
        (',' : s4) -> loop ((key, value) : acc) s4
        ('}' : s4) -> Right (JObj (reverse ((key, value) : acc)), s4)
        junk       -> Left ("expected ',' or '}' in object, found: " ++ take 20 junk)