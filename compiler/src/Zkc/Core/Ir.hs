-- | The typed Core IR: an SSA-style constraint graph.
--
-- This is the single most consequential design decision in the project, so
-- it is worth stating plainly: __the IR is not R1CS with sugar__. It is an
-- arithmetization-agnostic graph of field operations, hints and assertions.
--
-- R1CS is an unordered system of rank-1 equations over one global witness
-- vector. AIR (what a FRI\/STARK prover consumes) is an execution-trace table
-- with transition constraints between adjacent rows. They are structurally
-- different, and an IR shaped like either one cannot be lowered to the other.
-- Keeping the IR neutral is what lets phase 5 add a hand-written FRI backend
-- without touching the frontend.
--
-- Wire 0 is always the constant 1.
module Zkc.Core.Ir
  ( WireId
  , Visibility(..)
  , IrInput(..)
  , HintKind(..)
  , Op(..)
  , Node(..)
  , Assertion(..)
  , Ir(..)
  , constOneWire
  , opArgs
  , isHint
  ) where

import Zkc.Syntax.Ast (Visibility(..))

type WireId = Int

-- | Wire 0 is reserved for the field constant 1.
constOneWire :: WireId
constOneWire = 0

data IrInput = IrInput
  { iiWire :: WireId
  , iiName :: String
  , iiVisibility :: Visibility
  } deriving (Eq, Show)

data HintKind = KInvOrZero | KInv
  deriving (Eq, Ord, Show)

data Op
  = OConst Integer
  | OAdd WireId WireId
  | OSub WireId WireId
  | OMul WireId WireId
  | ONeg WireId
  -- | A value the witness generator computes but that no constraint yet
  -- pins down. Every hint is a proof obligation: phase 2's determinacy pass
  -- must show that the assertions determine it uniquely.
  -- | Carries the source-level advice name so backends and error
  -- messages can talk about @inv@ rather than @wire 3@ — and so a prover
  -- can explicitly override it (which is exactly what an attacker does).
  | OHint HintKind String [WireId]
  deriving (Eq, Ord, Show)

data Node = Node
  { nWire :: WireId
  , nOp :: Op
  } deriving (Eq, Show)

data Assertion = Assertion
  { aLhs :: WireId
  , aRhs :: WireId
  , aLabel :: String   -- ^ the source text, so backend errors name the equation
  , aLine :: Int
  } deriving (Eq, Show)

data Ir = Ir
  { irName :: String
  , irField :: String        -- ^ named field, e.g. @bn254@ — never hardcoded
  , irInputs :: [IrInput]
  , irNodes :: [Node]        -- ^ topologically ordered: args always precede
  , irAssertions :: [Assertion]
  } deriving (Eq, Show)

opArgs :: Op -> [WireId]
opArgs op = case op of
  OConst _   -> []
  OAdd a b   -> [a, b]
  OSub a b   -> [a, b]
  OMul a b   -> [a, b]
  ONeg a     -> [a]
  OHint _ _ as -> as

isHint :: Op -> Bool
isHint (OHint _ _ _) = True
isHint _ = False