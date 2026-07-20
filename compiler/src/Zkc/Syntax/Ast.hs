-- | The surface syntax tree.
--
-- The language is deliberately tiny in phase 1: one circuit, field-typed
-- wires, three statement forms. It is *not* Turing complete and never will
-- be — circuits are finite, so there is no unbounded recursion and every
-- loop (once loops exist) must be statically unrollable.
module Zkc.Syntax.Ast
  ( Visibility(..)
  , ParamDecl(..)
  , Hint(..)
  , Expr(..)
  , Stmt(..)
  , Circuit(..)
  , exprSpan
  ) where

-- | Whether an input is revealed to the verifier.
data Visibility = Private | Public
  deriving (Eq, Show)

-- | An input declaration: @private x: field;@
data ParamDecl = ParamDecl
  { pdName :: String
  , pdVisibility :: Visibility
  , pdLine :: Int
  } deriving (Eq, Show)

-- | Hint functions usable on the right of @advice@.
--
-- These are the *only* places a value may be computed without being
-- constrained, which is why they are a closed set rather than arbitrary
-- expressions: every one of them is a known proof obligation for phase 2.
data Hint
  = HintInvOrZero Expr  -- ^ @1\/x@, or 0 when @x == 0@
  | HintInv Expr        -- ^ @1\/x@; the witness solver fails when @x == 0@
  deriving (Eq, Show)

data Expr
  = ELit Integer Int      -- ^ field literal
  | EVar String Int       -- ^ variable reference
  | EAdd Expr Expr Int
  | ESub Expr Expr Int
  | EMul Expr Expr Int
  | ENeg Expr Int
  deriving (Eq, Show)

-- | Source line an expression starts on, for error messages.
exprSpan :: Expr -> Int
exprSpan e = case e of
  ELit _ l   -> l
  EVar _ l   -> l
  EAdd _ _ l -> l
  ESub _ _ l -> l
  EMul _ _ l -> l
  ENeg _ l   -> l

data Stmt
  -- | @let name = expr;@ — computes AND constrains. The only binding form
  -- ordinary circuit code needs, and the reason such code is sound by
  -- construction.
  = SLet String Expr Int
  -- | @advice name = hint(..);@ — computes WITHOUT constraining. The
  -- @unsafe@ of ZK: legal, but the value is not determined until some
  -- assertion pins it down.
  | SAdvice String Hint Int
  -- | @assert lhs == rhs;@ — emits a constraint.
  | SAssert Expr Expr Int
  deriving (Eq, Show)

data Circuit = Circuit
  { circName :: String
  , circParams :: [ParamDecl]
  , circBody :: [Stmt]
  } deriving (Eq, Show)