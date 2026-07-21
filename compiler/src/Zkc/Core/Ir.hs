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
  , HintInfo(..)
  , Op(..)
  , Node(..)
  , Assertion(..)
  , Ir(..)
  , InstanceSite(..)
  , Body(..)
  , constOneWire
  , opArgs
  , isHint
  , adviceWires
  , adviceDerived
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Zkc.Syntax.Ast (Visibility(..))

type WireId = Int

-- | Wire 0 is reserved for the field constant 1.
constOneWire :: WireId
constOneWire = 0

data IrInput = IrInput
  { iiWire :: WireId
  , iiName :: String
  , iiVisibility :: Visibility
  , iiLine :: Int          -- ^ where it was declared, for diagnostics
  } deriving (Eq, Show)

data HintKind = KInvOrZero | KInv
  deriving (Eq, Ord, Show)

-- | Everything a hint node carries besides its arguments.
--
-- The gadget name is not decoration: raw advice is only legal inside a
-- @gadget@ block, so recording which one a hint came from lets diagnostics
-- point at the quarantined region that owes the proof obligation.
data HintInfo = HintInfo
  { hiKind :: HintKind
  , hiName :: String     -- ^ source-level advice name
  , hiGadget :: String   -- ^ the enclosing gadget block
  , hiLine :: Int
  } deriving (Eq, Ord, Show)

data Op
  = OConst Integer
  | OAdd WireId WireId
  | OSub WireId WireId
  | OMul WireId WireId
  | ONeg WireId
  -- | A value the witness generator computes but that no constraint yet
  -- pins down. Every hint is a proof obligation: phase 2's determinacy pass
  -- must show that the assertions determine it uniquely.
  -- | A value the witness generator computes but that no constraint pins
  -- down on its own. Every hint is a proof obligation: the determinacy pass
  -- must show the assertions leave the circuit's outputs unique anyway.
  | OHint HintInfo [WireId]
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

-- | A retained gadget instantiation, the unit of /compositional/ determinacy.
--
-- The flat 'Ir' inlines every gadget away, which is all the backend needs.
-- But the determinacy pass must not re-expand a gadget per call site — that is
-- what blows the monomial budget on a deep Merkle path. So elaboration keeps,
-- alongside the flat IR, the shape of each call: which gadget, the wires its
-- arguments landed on, and the wires its results landed on. The proof then
-- applies the gadget's /summary/ here instead of expanding its body.
data InstanceSite = InstanceSite
  { isGadget :: String
  , isArgs :: [WireId]     -- ^ argument wires, in parameter order
  , isResults :: [WireId]  -- ^ result wires, in result order
  , isLine :: Int
  } deriving (Eq, Show)

-- | The determinacy-facing view of a scope (a gadget body or the circuit).
--
-- It separates a scope's /own/ primitive content — the nodes and assertions
-- written directly in it — from the gadget instances it contains, which are
-- handled by summary rather than expansion. Atoms are the input wires plus any
-- instance-result wires (values the scope does not compute itself).
data Body = Body
  { bodyParams :: [WireId]        -- ^ determined on entry (a gadget's params, or the circuit's non-output inputs)
  , bodyResultTargets :: [WireId] -- ^ wires that must be proved determined
  , bodyRequires :: [WireId]      -- ^ param wires assumed nonzero (from @require@)
  , bodyAtoms :: [IrInput]        -- ^ every atom in scope, for naming and taint
  , bodyNodes :: [Node]           -- ^ own nodes only (not inside nested instances)
  , bodyAsserts :: [Assertion]    -- ^ own assertions only
  , bodyInstances :: [InstanceSite]
  } deriving (Eq, Show)

opArgs :: Op -> [WireId]
opArgs op = case op of
  OConst _   -> []
  OAdd a b   -> [a, b]
  OSub a b   -> [a, b]
  OMul a b   -> [a, b]
  ONeg a     -> [a]
  OHint _ as -> as

isHint :: Op -> Bool
isHint (OHint _ _) = True
isHint _ = False

-- | Advice wires, paired with their hint metadata.
adviceWires :: Ir -> [(WireId, HintInfo)]
adviceWires ir =
  [ (nWire n, info) | n <- irNodes ir, OHint info _ <- [nOp n] ]

-- | Wires whose value depends, transitively, on a hint.
--
-- This is the *syntactic* taint, and it is deliberately distinct from
-- determinacy. A tainted wire may still be perfectly determined (@inv@ is,
-- whenever @x /= 0@), and an untainted one is determined by construction.
-- Conflating the two is what makes naive checkers reject correct circuits.
adviceDerived :: Ir -> Set.Set WireId
adviceDerived ir = foldl step Set.empty (irNodes ir)
  where
    step tainted node
      | isHint (nOp node) = Set.insert (nWire node) tainted
      | any (`Set.member` tainted) (opArgs (nOp node)) = Set.insert (nWire node) tainted
      | otherwise = tainted