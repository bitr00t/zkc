-- | Recursive-descent parser.
--
-- Grammar (phase 3):
--
-- @
--   program   ::= item* EOF                       -- exactly one circuit
--   item      ::= gadgetDef | circuit
--   gadgetDef ::= 'gadget' Ident '(' params ')' '->' '(' params ')'
--                 '{' require* stmt* '}'
--   circuit   ::= 'circuit' Ident '{' cparam* stmt* '}'
--   cparam    ::= ('private' | 'public' | 'output') Ident ':' 'field' ';'
--   require   ::= 'require' Ident '!=' '0' ';'
--   stmt      ::= 'let' Ident '=' expr ';'
--              |  'let' '(' names ')' '=' Ident '(' args ')' ';'  -- fresh results
--              |  '(' names ')' '=' Ident '(' args ')' ';'        -- bind outputs
--              |  'advice' Ident '=' hint ';'      -- only inside a gadget
--              |  'assert' expr '==' expr ';'
--   hint      ::= ('inv_or_zero' | 'inv') '(' expr ')'
--   expr      ::= term (('+' | '-') term)*
--   term      ::= factor ('*' factor)*
--   factor    ::= Number | Ident | '(' expr ')' | '-' factor
-- @
--
-- The one piece of lookahead worth naming: a @let@ followed by @(@ is an
-- instance with fresh results; a @let@ followed by an identifier is an
-- ordinary scalar binding. Instantiation is always a statement, never a
-- sub-expression, so elaboration never has to inline inside an expression
-- tree.
module Zkc.Syntax.Parser (parseProgram, parseCircuit) where

import Zkc.Diagnostics
import Zkc.Syntax.Ast
import Zkc.Syntax.Lexer

-- | Parse a whole source file into a program.
parseProgram :: String -> Either Diagnostic Program
parseProgram source = do
  tokens <- lexer source
  (items, rest) <- pItems tokens
  case rest of
    (Token TEof _ : _) -> assemble items
    (Token t l : _) ->
      Left $ diagAt l ("unexpected " ++ describeTok t ++ " at the top level")
    [] -> assemble items

-- | Back-compat shim: a few call sites and tests still speak in terms of a
-- single circuit. A program's circuit is what they want.
parseCircuit :: String -> Either Diagnostic Circuit
parseCircuit source = progCircuit <$> parseProgram source

-- | A parsed top-level item is either a gadget definition or the circuit.
data Item = IGadget GadgetDef | ICircuit Circuit

assemble :: [Item] -> Either Diagnostic Program
assemble items =
  case [ c | ICircuit c <- items ] of
    [circuit] -> Right (Program [ g | IGadget g <- items ] circuit)
    []        -> Left $ diag "a source file must contain exactly one 'circuit'; none found"
    _         -> Left $ diag "a source file must contain exactly one 'circuit'; found several"

type P a = [Token] -> Either Diagnostic (a, [Token])

pItems :: P [Item]
pItems tokens = case tokens of
  (Token TGadget _ : _) -> do
    (g, rest) <- pGadgetDef tokens
    (more, rest') <- pItems rest
    Right (IGadget g : more, rest')
  (Token TCircuit _ : _) -> do
    (c, rest) <- pCircuit tokens
    (more, rest') <- pItems rest
    Right (ICircuit c : more, rest')
  _ -> Right ([], tokens)

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

-- Gadget definitions ---------------------------------------------------

pGadgetDef :: P GadgetDef
pGadgetDef tokens0 = do
  ((), t1) <- expect TGadget "at the start of a gadget definition" tokens0
  ((name, line), t2) <- pIdent "a gadget name" t1
  ((), t3) <- expect TLParen "after the gadget name" t2
  (params, t4) <- pFieldNames t3
  ((), t5) <- expect TRParen "to close the parameter list" t4
  ((), t6) <- expect TArrow "after the parameter list" t5
  ((), t7) <- expect TLParen "before the result list" t6
  (results, t8) <- pFieldNames t7
  ((), t9) <- expect TRParen "to close the result list" t8
  ((), t10) <- expect TLBrace "before the gadget body" t9
  (requires, t11) <- pRequires t10
  (body, t12) <- pStmts t11
  ((), t13) <- expect TRBrace "to close the gadget body" t12
  Right (GadgetDef name params results requires body line, t13)

-- | A comma-separated list of @Ident ':' 'field'@, possibly empty.
pFieldNames :: P [String]
pFieldNames tokens = case tokens of
  (Token (TIdent _) _ : _) -> do
    ((name, _), t1) <- pIdent "a name" tokens
    ((), t2) <- expect TColon "after the name" t1
    ((), t3) <- expect TField "as the type" t2
    (more, t4) <- pFieldTail t3
    Right (name : more, t4)
  _ -> Right ([], tokens)
  where
    pFieldTail (Token TComma _ : rest) = do
      ((name, _), t1) <- pIdent "a name" rest
      ((), t2) <- expect TColon "after the name" t1
      ((), t3) <- expect TField "as the type" t2
      (more, t4) <- pFieldTail t3
      Right (name : more, t4)
    pFieldTail ts = Right ([], ts)

pRequires :: P [Require]
pRequires (Token TRequire line : rest) = do
  ((name, _), t1) <- pIdent "a parameter name after 'require'" rest
  ((), t2) <- expect TNe "in the precondition (only '!= 0' is supported)" t1
  ((), t3) <- expectZero t2
  ((), t4) <- expect TSemi "after the precondition" t3
  (more, t5) <- pRequires t4
  Right (Require name line : more, t5)
pRequires tokens = Right ([], tokens)

-- | Preconditions are @!= 0@ only, so the right-hand side must be @0@.
expectZero :: P ()
expectZero (Token (TNumber 0) _ : rest) = Right ((), rest)
expectZero (Token got line : _) =
  Left $ diagAt line $
    "a precondition must be '!= 0', found " ++ describeTok got
    ++ " on the right-hand side"
expectZero [] = Left $ diag "unexpected end of input in a precondition"

-- Circuit --------------------------------------------------------------

pCircuit :: P Circuit
pCircuit tokens0 = do
  ((), tokens1) <- expect TCircuit "at the start of the circuit" tokens0
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

-- Statements -----------------------------------------------------------

pStmts :: P [Stmt]
pStmts tokens = case tokens of
  (Token TLet line : Token TLParen _ : rest) -> do
    -- let (r, ..) = g(args);  — fresh-result instance
    (names, t1) <- pNames rest
    ((), t2) <- expect TEq "after the result names" t1
    (stmt, t3) <- pInstanceCall (BindFresh names) line t2
    (more, t4) <- pStmts t3
    Right (stmt : more, t4)

  (Token TLet line : rest) -> do
    ((name, _), t1) <- pIdent "a binding name" rest
    ((), t2) <- expect TEq "after the binding name" t1
    (body, t3) <- pExpr t2
    ((), t4) <- expect TSemi "after the let binding" t3
    (more, t5) <- pStmts t4
    Right (SLet name body line : more, t5)

  (Token TLParen line : rest) -> do
    -- (o, ..) = g(args);  — bind existing outputs
    (names, t1) <- pNames rest
    ((), t2) <- expect TEq "after the result names" t1
    (stmt, t3) <- pInstanceCall (BindExisting names) line t2
    (more, t4) <- pStmts t3
    Right (stmt : more, t4)

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

  (Token TRequire line : _) ->
    Left $ diagAt line
      "'require' may only appear at the top of a gadget body, before any statement"

  _ -> Right ([], tokens)

-- | Parse @Ident '(' args ')' ';'@ into an instance statement, given the
-- already-parsed binding and the statement's line.
pInstanceCall :: InstanceBind -> Int -> P Stmt
pInstanceCall bind line tokens = do
  ((gadget, _), t1) <- pIdent "a gadget name to instantiate" tokens
  ((), t2) <- expect TLParen ("after gadget '" ++ gadget ++ "'") t1
  (args, t3) <- pArgs t2
  ((), t4) <- expect TRParen "to close the argument list" t3
  ((), t5) <- expect TSemi "after the instantiation" t4
  Right (SInstance bind gadget args line, t5)

-- | A parenthesised comma-separated list of names, already past the '('.
pNames :: P [String]
pNames tokens = do
  ((first, _), t1) <- pIdent "a result name" tokens
  loop [first] t1
  where
    loop acc (Token TComma _ : rest) = do
      ((name, _), t1) <- pIdent "a result name" rest
      loop (acc ++ [name]) t1
    loop acc (Token TRParen _ : rest) = Right (acc, rest)
    loop _ (Token got line : _) =
      Left $ diagAt line ("expected ',' or ')' in the result list, found " ++ describeTok got)
    loop _ [] = Left $ diag "unexpected end of input in a result list"

-- | Argument expressions, already past the '('. May be empty.
pArgs :: P [Expr]
pArgs tokens@(Token TRParen _ : _) = Right ([], tokens)
pArgs tokens = do
  (first, t1) <- pExpr tokens
  loop [first] t1
  where
    loop acc (Token TComma _ : rest) = do
      (next, t1) <- pExpr rest
      loop (acc ++ [next]) t1
    loop acc ts = Right (acc, ts)

pHint :: P Hint
pHint (Token (TIdent name) line : rest) = do
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