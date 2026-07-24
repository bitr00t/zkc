-- | Hand-rolled lexer.
--
-- No lexer generator and no external dependencies: the compiler builds with
-- nothing but GHC's boot libraries, which keeps the toolchain story trivial
-- (@make@ and go) and the whole pipeline auditable.
--
-- Every token records both the line and the 1-based column it starts on
-- (phase 6, J.2). The column is what lets a diagnostic point a caret at the
-- exact offending character rather than only naming the line.
module Zkc.Syntax.Lexer
  ( Token(..)
  , Tok(..)
  , lexer
  , describeTok
  ) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isSpace)

import Zkc.Diagnostics (Diagnostic, diagAtCol)

-- | A token plus the line and column it was found on (for error messages).
data Token = Token { tokKind :: Tok, tokLine :: Int, tokCol :: Int }
  deriving (Eq, Show)

data Tok
  = TCircuit | TPrivate | TPublic | TOutput | TField | TGadget
  | TLet | TAdvice | TAssert | TRequire
  | TIdent String
  | TNumber Integer
  | TLBrace | TRBrace | TLParen | TRParen
  | TColon | TSemi | TComma
  | TPlus | TMinus | TStar | TEqEq | TEq | TNe
  | TArrow
  | TEof
  deriving (Eq, Show)

-- | Human-readable token name, used in @expected X, found Y@ messages.
describeTok :: Tok -> String
describeTok t = case t of
  TCircuit  -> "'circuit'"
  TPrivate  -> "'private'"
  TPublic   -> "'public'"
  TOutput   -> "'output'"
  TGadget   -> "'gadget'"
  TField    -> "'field'"
  TLet      -> "'let'"
  TAdvice   -> "'advice'"
  TAssert   -> "'assert'"
  TRequire  -> "'require'"
  TIdent s  -> "identifier '" ++ s ++ "'"
  TNumber n -> "number " ++ show n
  TLBrace   -> "'{'"
  TRBrace   -> "'}'"
  TLParen   -> "'('"
  TRParen   -> "')'"
  TColon    -> "':'"
  TSemi     -> "';'"
  TComma    -> "','"
  TPlus     -> "'+'"
  TMinus    -> "'-'"
  TStar     -> "'*'"
  TEqEq     -> "'=='"
  TEq       -> "'='"
  TNe       -> "'!='"
  TArrow    -> "'->'"
  TEof      -> "end of input"

-- | Tokenize, or fail with a line- and column-annotated diagnostic. Columns
-- are 1-based; a newline resets the column and advances the line.
lexer :: String -> Either Diagnostic [Token]
lexer = go 1 1
  where
    go :: Int -> Int -> String -> Either Diagnostic [Token]
    go line col [] = Right [Token TEof line col]
    go line col s@(c:cs)
      | c == '\n' = go (line + 1) 1 cs
      | isSpace c = go line (col + 1) cs
      -- line comments: skip to the end of the line; the newline reset follows.
      | c == '/', ('/':rest) <- cs = go line col (dropWhile (/= '\n') rest)
      | isDigit c =
          let (digits, rest) = span isDigit s
          in (Token (TNumber (read digits)) line col :) <$> go line (col + length digits) rest
      | isAlpha c || c == '_' =
          let (word, rest) = span (\x -> isAlphaNum x || x == '_') s
          in (Token (keyword word) line col :) <$> go line (col + length word) rest
      | otherwise = symbol line col s

    keyword w = case w of
      "circuit" -> TCircuit
      "private" -> TPrivate
      "public"  -> TPublic
      "output"  -> TOutput
      "gadget"  -> TGadget
      "field"   -> TField
      "let"     -> TLet
      "advice"  -> TAdvice
      "assert"  -> TAssert
      "require" -> TRequire
      _         -> TIdent w

    -- Each symbol emits at the current column and advances by its own width.
    symbol line col s = case s of
      ('=':'=':rest) -> (Token TEqEq line col :)   <$> go line (col + 2) rest
      ('!':'=':rest) -> (Token TNe line col :)     <$> go line (col + 2) rest
      ('-':'>':rest) -> (Token TArrow line col :)  <$> go line (col + 2) rest
      ('{':rest)     -> (Token TLBrace line col :) <$> go line (col + 1) rest
      ('}':rest)     -> (Token TRBrace line col :) <$> go line (col + 1) rest
      ('(':rest)     -> (Token TLParen line col :) <$> go line (col + 1) rest
      (')':rest)     -> (Token TRParen line col :) <$> go line (col + 1) rest
      (':':rest)     -> (Token TColon line col :)  <$> go line (col + 1) rest
      (';':rest)     -> (Token TSemi line col :)   <$> go line (col + 1) rest
      (',':rest)     -> (Token TComma line col :)  <$> go line (col + 1) rest
      ('+':rest)     -> (Token TPlus line col :)   <$> go line (col + 1) rest
      ('-':rest)     -> (Token TMinus line col :)  <$> go line (col + 1) rest
      ('*':rest)     -> (Token TStar line col :)   <$> go line (col + 1) rest
      ('=':rest)     -> (Token TEq line col :)     <$> go line (col + 1) rest
      (ch:_)         -> Left $ diagAtCol line col ("unexpected character " ++ show ch)
      []             -> go line col []