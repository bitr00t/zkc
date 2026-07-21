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

-- | The role a declared wire plays.
--
-- Phase 1 had only @private@ and @public@, which conflated two different
-- things and made the central question of phase 2 ill-posed. \"Is this value
-- determined?\" only has an answer once you know whether the circuit is
-- meant to /compute/ it.
--
--   * 'Private' — a secret input. Known to the prover only.
--   * 'Public'  — an input the verifier also sees. Still an /input/: the
--     prover supplies it, and it need not be determined by anything. A
--     circuit asserting @a * b == 12@ with both public is a perfectly
--     sound \"I know a factorisation\" statement.
--   * 'Output'  — a value the circuit /computes/. The determinacy pass must
--     prove it is a function of the inputs; if two different outputs can
--     satisfy the constraints, the prover chooses which falsehood to prove.
--
-- Outputs are public to the verifier, like 'Public'; the difference is the
-- proof obligation attached to them.
data Visibility = Private | Public | Output
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
  -- | @gadget name { .. }@ — the quarantine for raw advice.
  --
  -- Outside a gadget, @advice@ is a compile error. Inside one, it is
  -- allowed but every declared output still has to be proved determined,
  -- so the block is an explicit \"I am doing something subtle here\"
  -- marker rather than an escape hatch.
  --
  -- Phase-2 gadgets are markers, not scopes: bindings inside are visible
  -- outside. Phase 3 turns them into reusable parameterised definitions.
  | SGadget String [Stmt] Int
  deriving (Eq, Show)

data Circuit = Circuit
  { circName :: String
  , circParams :: [ParamDecl]
  , circBody :: [Stmt]
  } deriving (Eq, Show)