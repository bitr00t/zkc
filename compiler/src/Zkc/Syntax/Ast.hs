-- | The surface syntax tree.
--
-- The language is deliberately tiny and *not* Turing complete: circuits are
-- finite, so there is no unbounded recursion and every loop (once loops
-- exist) must be statically unrollable.
--
-- Phase 3 turns gadgets from inline markers into top-level, parameterised
-- __definitions__. A source file is now a 'Program': zero or more
-- 'GadgetDef's plus exactly one 'Circuit'. A gadget has parameters (wires
-- the caller supplies), results (wires the caller allocates and the body
-- constrains — output-parameters, so they fit the IR's \"declared atom
-- pinned by assertions\" shape exactly), and 'Require' preconditions. It is
-- reached from a call site, and each call is inlined with a fresh scope.
module Zkc.Syntax.Ast
  ( Visibility(..)
  , ParamDecl(..)
  , Hint(..)
  , Expr(..)
  , Stmt(..)
  , InstanceBind(..)
  , Require(..)
  , GadgetDef(..)
  , Circuit(..)
  , Program(..)
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
  -- @unsafe@ of ZK: legal only inside a gadget definition, and the value is
  -- not determined until some assertion pins it down.
  | SAdvice String Hint Int
  -- | @assert lhs == rhs;@ — emits a constraint.
  | SAssert Expr Expr Int
  -- | A gadget instantiation. Either
  --
  --   * @(o, ..) = g(args);@   — bind results to already-declared outputs
  --     (or, inside a gadget body, to the enclosing gadget's own results);
  --   * @let (r, ..) = g(args);@ — allocate fresh result wires.
  --
  -- The call is inlined at elaboration with a fresh scope. Determinacy does
  -- /not/ re-expand it: the gadget's proved summary is applied instead.
  | SInstance InstanceBind String [Expr] Int
  deriving (Eq, Show)

-- | How an instance binds its results.
data InstanceBind
  = BindExisting [String]   -- ^ @(o, ..) = g(args);@
  | BindFresh [String]      -- ^ @let (r, ..) = g(args);@
  deriving (Eq, Show)

-- | A gadget precondition: @require name != 0;@.
--
-- It is both an assumption the gadget's determinacy proof may lean on and an
-- obligation each call site must discharge from its own nonzero context.
data Require = Require
  { rqName :: String
  , rqLine :: Int
  } deriving (Eq, Show)

-- | A parameterised, reusable gadget.
--
-- Parameters and results are all field-typed. Results are output-parameters:
-- the caller allocates the wire, the body constrains it — which is exactly
-- the shape the IR already uses for a circuit's declared outputs, so nothing
-- downstream has to learn a new concept.
data GadgetDef = GadgetDef
  { gdName :: String
  , gdParams :: [String]
  , gdResults :: [String]
  , gdRequires :: [Require]
  , gdBody :: [Stmt]
  , gdLine :: Int
  } deriving (Eq, Show)

data Circuit = Circuit
  { circName :: String
  , circParams :: [ParamDecl]
  , circBody :: [Stmt]
  } deriving (Eq, Show)

-- | A whole source file: the gadget definitions plus the one circuit.
data Program = Program
  { progGadgets :: [GadgetDef]
  , progCircuit :: Circuit
  } deriving (Eq, Show)