-- | Hand-rolled lexer.
--
-- No lexer generator and no external dependencies: the compiler builds with
-- nothing but GHC's boot libraries, which keeps the toolchain story trivial
-- (@make@ and go) and the whole pipeline auditable.
module Zkc.Syntax.Lexer
  ( Token(..)
  , Tok(..)
  , lexer
  , describeTok
  ) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isSpace)

import Zkc.Diagnostics (Diagnostic, diagAt)

-- | A token plus the line it was found on (for error messages).
data Token = Token { tokKind :: Tok, tokLine :: Int }
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

-- | Tokenize, or fail with a line-annotated diagnostic.
lexer :: String -> Either Diagnostic [Token]
lexer = go 1
  where
    go :: Int -> String -> Either Diagnostic [Token]
    go line [] = Right [Token TEof line]
    go line s@(c:cs)
      | c == '\n' = go (line + 1) cs
      | isSpace c = go line cs
      -- line comments
      | c == '/', ('/':rest) <- cs = go line (dropWhile (/= '\n') rest)
      | isDigit c =
          let (digits, rest) = span isDigit s
          in (Token (TNumber (read digits)) line :) <$> go line rest
      | isAlpha c || c == '_' =
          let (word, rest) = span (\x -> isAlphaNum x || x == '_') s
          in (Token (keyword word) line :) <$> go line rest
      | otherwise = symbol line s

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

    symbol line s = case s of
      ('=':'=':rest) -> (Token TEqEq line :)   <$> go line rest
      ('!':'=':rest) -> (Token TNe line :)     <$> go line rest
      ('-':'>':rest) -> (Token TArrow line :)  <$> go line rest
      ('{':rest)     -> (Token TLBrace line :) <$> go line rest
      ('}':rest)     -> (Token TRBrace line :) <$> go line rest
      ('(':rest)     -> (Token TLParen line :) <$> go line rest
      (')':rest)     -> (Token TRParen line :) <$> go line rest
      (':':rest)     -> (Token TColon line :)  <$> go line rest
      (';':rest)     -> (Token TSemi line :)   <$> go line rest
      (',':rest)     -> (Token TComma line :)  <$> go line rest
      ('+':rest)     -> (Token TPlus line :)   <$> go line rest
      ('-':rest)     -> (Token TMinus line :)  <$> go line rest
      ('*':rest)     -> (Token TStar line :)   <$> go line rest
      ('=':rest)     -> (Token TEq line :)     <$> go line rest
      (c:_)          -> Left $ diagAt line ("unexpected character " ++ show c)
      []             -> go line []