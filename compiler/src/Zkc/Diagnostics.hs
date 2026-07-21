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
  , withNotes
  , withHelp
  , render
  ) where

data Diagnostic = Diagnostic
  { diagMessage :: String
  , diagLine :: Maybe Int
  , diagNotes :: [String]
  , diagHelp :: Maybe String
  } deriving (Eq, Show)

diag :: String -> Diagnostic
diag message = Diagnostic message Nothing [] Nothing

diagAt :: Int -> String -> Diagnostic
diagAt line message = Diagnostic message (Just line) [] Nothing

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
        in [ "  --> " ++ path ++ ":" ++ show line
           , "   " ++ gutter ++ " |"
           , "   " ++ show line ++ " | " ++ text
           , "   " ++ gutter ++ " |"
           ]

    notes = [ "     = " ++ note | note <- diagNotes d ]
    help = case diagHelp d of
      Nothing -> []
      Just text -> ["help: " ++ text]