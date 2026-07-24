-- | Compiler diagnostics.
--
-- Error messages are a feature of this compiler, not an afterthought. A
-- circuit author who is told \"constraint 7 failed\" learns nothing; one who
-- is shown the offending line, the value that is not pinned down, and the
-- assumption under which it stays free can actually fix the bug.
--
-- Every error therefore carries an optional source line (echoed back), notes
-- that explain the reasoning, and an optional suggestion.
module Zkc.Diagnostics
  ( Diagnostic(..)
  , diag
  , diagAt
  , diagAtCol
  , withNotes
  , withHelp
  , render
  , renderJson
  , parseDiagnostic
  , diagnosticToJson
  , diagnosticFromJson
  ) where

import Zkc.Json (Json(..), encode, parse)

data Diagnostic = Diagnostic
  { diagMessage :: String
  , diagLine :: Maybe Int
  , diagCol :: Maybe Int   -- ^ 1-based column, when a token pinned it (J.2)
  , diagNotes :: [String]
  , diagHelp :: Maybe String
  } deriving (Eq, Show)

diag :: String -> Diagnostic
diag message = Diagnostic message Nothing Nothing [] Nothing

diagAt :: Int -> String -> Diagnostic
diagAt line message = Diagnostic message (Just line) Nothing [] Nothing

-- | A diagnostic pinned to a line /and/ a column, so 'render' can point a
-- caret at the exact character (phase 6, J.2).
diagAtCol :: Int -> Int -> String -> Diagnostic
diagAtCol line col message = Diagnostic message (Just line) (Just col) [] Nothing

withNotes :: [String] -> Diagnostic -> Diagnostic
withNotes notes d = d { diagNotes = diagNotes d ++ notes }

withHelp :: String -> Diagnostic -> Diagnostic
withHelp help d = d { diagHelp = Just help }

-- | Render a diagnostic against the source it came from.
--
-- >  error: output 'out' is not determined by the circuit's inputs
-- >    --> examples/iszero_broken.zkc:5
-- >     |
-- >   5 |     output out: field;
-- >     |
-- >     = under the assumption x != 0, more than one value satisfies
-- >   help: add a constraint that forces 'out' in that case
render :: FilePath -> String -> Diagnostic -> String
render path source d = unlines (header ++ snippet ++ notes ++ help)
  where
    header = ["error: " ++ diagMessage d]

    snippet = case diagLine d of
      Nothing -> ["  --> " ++ path]
      Just line ->
        let gutter = replicate (length (show line)) ' '
            sourceLines = lines source
            text = if line >= 1 && line <= length sourceLines
                     then sourceLines !! (line - 1)
                     else ""
            locus = case diagCol d of
              Just col -> ":" ++ show col
              Nothing -> ""
            -- A caret under the exact column, when one was recorded.
            caret = case diagCol d of
              Just col -> ["   " ++ gutter ++ " | " ++ replicate (col - 1) ' ' ++ "^"]
              Nothing -> []
        in [ "  --> " ++ path ++ ":" ++ show line ++ locus
           , "   " ++ gutter ++ " |"
           , "   " ++ show line ++ " | " ++ text
           ]
           ++ caret
           ++ [ "   " ++ gutter ++ " |" ]

    notes = [ "     = " ++ note | note <- diagNotes d ]
    help = case diagHelp d of
      Nothing -> []
      Just text -> ["help: " ++ text]
-- JSON form ------------------------------------------------------------
--
-- The same diagnostic that 'render' formats for a human is also emitted as a
-- structured value, so an editor or a language server can consume it without
-- scraping text. This is the smallest, most isolated piece of phase 6, and
-- everything else in the phase (the LSP, the profiler's per-line report)
-- depends on structured diagnostics existing. The mapping is a faithful
-- serialisation of the record: message, an optional line (null when absent),
-- the notes in order, and an optional help string.

-- | The diagnostic as a JSON value.
diagnosticToJson :: Diagnostic -> Json
diagnosticToJson d = JObj
  [ ("message", JStr (diagMessage d))
  , ("line", maybe JNull (JInt . fromIntegral) (diagLine d))
  , ("col", maybe JNull (JInt . fromIntegral) (diagCol d))
  , ("notes", JArr (map JStr (diagNotes d)))
  , ("help", maybe JNull JStr (diagHelp d))
  ]

-- | Recover a diagnostic from its JSON value. The inverse of
-- 'diagnosticToJson', so the two round-trip.
diagnosticFromJson :: Json -> Either String Diagnostic
diagnosticFromJson value = case value of
  JObj fields -> do
    message <- lookupField "message" fields >>= asString
    line <- lookupField "line" fields >>= asOptInt
    col <- lookupField "col" fields >>= asOptInt
    notes <- lookupField "notes" fields >>= asStringArray
    help <- lookupField "help" fields >>= asOptString
    Right (Diagnostic message line col notes help)
  _ -> Left "a diagnostic must be a JSON object"
  where
    lookupField name fields = case lookup name fields of
      Just v -> Right v
      Nothing -> Left ("diagnostic is missing the '" ++ name ++ "' field")

    asString (JStr s) = Right s
    asString _ = Left "expected a string"

    asOptString JNull = Right Nothing
    asOptString (JStr s) = Right (Just s)
    asOptString _ = Left "expected a string or null"

    asOptInt JNull = Right Nothing
    asOptInt (JInt n) = Right (Just (fromIntegral n))
    asOptInt _ = Left "expected an integer or null"

    asStringArray (JArr xs) = mapM asString xs
    asStringArray _ = Left "expected an array of strings"

-- | Emit a diagnostic as a compact JSON string — the machine-readable
-- companion to 'render'.
renderJson :: Diagnostic -> String
renderJson = encode . diagnosticToJson

-- | Parse a diagnostic back from its JSON string.
parseDiagnostic :: String -> Either String Diagnostic
parseDiagnostic text = parse text >>= diagnosticFromJson