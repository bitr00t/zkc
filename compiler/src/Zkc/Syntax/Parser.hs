-- | Recursive-descent parser.
--
-- Grammar (phase 1):
--
-- @
--   circuit  ::= 'circuit' Ident '{' param* stmt* '}'
--   param    ::= ('private' | 'public' | 'output') Ident ':' 'field' ';'
--   stmt     ::= 'let' Ident '=' expr ';'
--              | 'advice' Ident '=' hint ';'          -- only inside a gadget
--              | 'assert' expr '==' expr ';'
--              | 'gadget' Ident '{' stmt* '}'
--   hint     ::= ('inv_or_zero' | 'inv') '(' expr ')'
--   expr     ::= term (('+' | '-') term)*
--   term     ::= factor ('*' factor)*
--   factor   ::= Number | Ident | '(' expr ')' | '-' factor
-- @
--
-- Two additions since phase 1: the @output@ role, which is what makes
-- \"determined by the inputs\" a well-posed question, and @gadget@ blocks,
-- which quarantine raw advice.
module Zkc.Syntax.Parser (parseCircuit) where

import Zkc.Diagnostics
import Zkc.Syntax.Ast
import Zkc.Syntax.Lexer

-- | Parse a whole source file into a circuit.
parseCircuit :: String -> Either Diagnostic Circuit
parseCircuit source = do
  tokens <- lexer source
  (circuit, rest) <- pCircuit tokens
  case rest of
    (Token TEof _ : _) -> Right circuit
    (Token t l : _) ->
      Left $ diagAt l ("unexpected " ++ describeTok t ++ " after the circuit body")
    [] -> Right circuit

type P a = [Token] -> Either Diagnostic (a, [Token])

expect :: Tok -> String -> P ()
expect want context (Token got line : rest)
  | got == want = Right ((), rest)
  | otherwise = Left $ diagAt line $
      "expected " ++ describeTok want ++ " " ++ context
      ++ ", found " ++ describeTok got
expect want _ [] = Left $ diag ("unexpected end of input, expected " ++ describeTok want)

pIdent :: String -> P (String, Int)
pIdent _ (Token (TIdent name) line : rest) = Right ((name, line), rest)
pIdent context (Token got line : _) =
  Left $ diagAt line ("expected " ++ context ++ ", found " ++ describeTok got)
pIdent context [] = Left $ diag ("unexpected end of input, expected " ++ context)

pCircuit :: P Circuit
pCircuit tokens0 = do
  ((), tokens1) <- expect TCircuit "at the start of the file" tokens0
  ((name, _), tokens2) <- pIdent "a circuit name" tokens1
  ((), tokens3) <- expect TLBrace "after the circuit name" tokens2
  (params, tokens4) <- pParams tokens3
  (body, tokens5) <- pStmts tokens4
  ((), tokens6) <- expect TRBrace "to close the circuit body" tokens5
  Right (Circuit name params body, tokens6)

-- | Parameter declarations must all precede the statements.
pParams :: P [ParamDecl]
pParams tokens = case tokens of
  (Token TPrivate line : rest) -> one Private line rest
  (Token TPublic line : rest) -> one Public line rest
  (Token TOutput line : rest) -> one Output line rest
  _ -> Right ([], tokens)
  where
    one visibility line rest = do
      ((name, _), t1) <- pIdent "a parameter name" rest
      ((), t2) <- expect TColon "after the parameter name" t1
      ((), t3) <- expect TField "as the parameter type" t2
      ((), t4) <- expect TSemi "after the parameter declaration" t3
      (more, t5) <- pParams t4
      Right (ParamDecl name visibility line : more, t5)

pStmts :: P [Stmt]
pStmts tokens = case tokens of
  (Token TLet line : rest) -> do
    ((name, _), t1) <- pIdent "a binding name" rest
    ((), t2) <- expect TEq "after the binding name" t1
    (body, t3) <- pExpr t2
    ((), t4) <- expect TSemi "after the let binding" t3
    (more, t5) <- pStmts t4
    Right (SLet name body line : more, t5)

  (Token TAdvice line : rest) -> do
    ((name, _), t1) <- pIdent "an advice name" rest
    ((), t2) <- expect TEq "after the advice name" t1
    (hint, t3) <- pHint t2
    ((), t4) <- expect TSemi "after the advice binding" t3
    (more, t5) <- pStmts t4
    Right (SAdvice name hint line : more, t5)

  (Token TAssert line : rest) -> do
    (lhs, t1) <- pExpr rest
    ((), t2) <- expect TEqEq "in the assertion" t1
    (rhs, t3) <- pExpr t2
    ((), t4) <- expect TSemi "after the assertion" t3
    (more, t5) <- pStmts t4
    Right (SAssert lhs rhs line : more, t5)

  (Token TGadget line : rest) -> do
    ((name, _), t1) <- pIdent "a gadget name" rest
    ((), t2) <- expect TLBrace "after the gadget name" t1
    (body, t3) <- pStmts t2
    ((), t4) <- expect TRBrace "to close the gadget block" t3
    (more, t5) <- pStmts t4
    Right (SGadget name body line : more, t5)

  _ -> Right ([], tokens)

pHint :: P Hint
pHint (Token (TIdent name) line : rest) = do
  -- Check the name *before* the parentheses so that `advice w = x * x;`
  -- reports the real problem ("that is not a hint") instead of complaining
  -- about a missing '('.
  build <- case name of
    "inv_or_zero" -> Right HintInvOrZero
    "inv" -> Right HintInv
    _ -> Left $ diagAt line $
      "'" ++ name ++ "' is not a known hint; the right-hand side of 'advice' "
      ++ "must be a hint call (phase 2 provides 'inv_or_zero' and 'inv')"
  ((), t1) <- expect TLParen ("after hint '" ++ name ++ "'") rest
  (argument, t2) <- pExpr t1
  ((), t3) <- expect TRParen "to close the hint argument" t2
  Right (build argument, t3)
pHint (Token got line : _) =
  Left $ diagAt line $
    "the right-hand side of 'advice' must be a hint call, found " ++ describeTok got
    ++ " (only hints may produce unconstrained values)"
pHint [] = Left $ diag "unexpected end of input in advice binding"

pExpr :: P Expr
pExpr tokens = do
  (first, rest) <- pTerm tokens
  loop first rest
  where
    loop acc (Token TPlus line : rest) = do
      (next, rest') <- pTerm rest
      loop (EAdd acc next line) rest'
    loop acc (Token TMinus line : rest) = do
      (next, rest') <- pTerm rest
      loop (ESub acc next line) rest'
    loop acc rest = Right (acc, rest)

pTerm :: P Expr
pTerm tokens = do
  (first, rest) <- pFactor tokens
  loop first rest
  where
    loop acc (Token TStar line : rest) = do
      (next, rest') <- pFactor rest
      loop (EMul acc next line) rest'
    loop acc rest = Right (acc, rest)

pFactor :: P Expr
pFactor tokens = case tokens of
  (Token (TNumber n) line : rest) -> Right (ELit n line, rest)
  (Token (TIdent name) line : rest) -> Right (EVar name line, rest)
  (Token TMinus line : rest) -> do
    (inner, rest') <- pFactor rest
    Right (ENeg inner line, rest')
  (Token TLParen _ : rest) -> do
    (inner, t1) <- pExpr rest
    ((), t2) <- expect TRParen "to close the parenthesised expression" t1
    Right (inner, t2)
  (Token got line : _) ->
    Left $ diagAt line ("expected an expression, found " ++ describeTok got)
  [] -> Left $ diag "unexpected end of input in expression"