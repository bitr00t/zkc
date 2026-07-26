-- | Per-source-line cost, for the editor.
--
-- The canonical profiler is the backend's @zkc-profile@: it lowers the IR to
-- both arithmetizations and counts. The language server cannot call it cheaply
-- on every keystroke — it is a separate Rust binary — so for inlay hints this
-- module reproduces the same /unfused/ accounting directly on the Haskell IR,
-- which now carries a source line on every node (L.1). The rules are the
-- backend's, kept deliberately trivial so the two cannot drift:
--
--   * R1CS: one constraint per multiplication, one per assertion.
--   * Plonkish: one row per arithmetic node (const/add/sub/mul/neg), one per
--     assertion.
--   * A hint costs nothing in either — it is an unconstrained value.
--
-- These are exactly the rules in @zkc-core@'s @lower_with(.., false)@ and
-- @lower_plonkish_with(.., false)@, so the per-line totals here match the
-- backend's unfused totals, which is the invariant @zkc-profile@ is tested on.
module Zkc.Profile
  ( LineCost(..)
  , lineCosts
  , profileSource
  ) where

import qualified Data.Map.Strict as Map

import Zkc.Core.Elaborate (elaborate, Elaborated(..))
import Zkc.Core.Ir
import Zkc.Syntax.Parser (parseProgram)

-- | One source line's cost in each arithmetization.
data LineCost = LineCost
  { lcLine :: Int
  , lcR1cs :: Int
  , lcPlonkish :: Int
  } deriving (Eq, Show)

-- | Attribute a flat IR's cost to source lines, unfused. Lines with no source
-- position (synthesised nodes, hints) are dropped rather than reported as
-- line 0.
lineCosts :: Ir -> [LineCost]
lineCosts ir =
  [ LineCost line r p
  | (line, (r, p)) <- Map.toAscList tallied
  , line /= 0
  ]
  where
    tallied = foldr addAssertion (foldr addNode Map.empty (irNodes ir)) (irAssertions ir)

    addNode node = case nOp node of
      OMul _ _  -> bump (nLine node) 1 1     -- a constraint and a row
      OConst _  -> bump (nLine node) 0 1     -- a row only
      OAdd _ _  -> bump (nLine node) 0 1
      OSub _ _  -> bump (nLine node) 0 1
      ONeg _    -> bump (nLine node) 0 1
      OHint _ _ -> id                         -- free in both

    addAssertion a = bump (aLine a) 1 1       -- a constraint and a row

    bump line dr dp = Map.insertWith addPair line (dr, dp)
    addPair (a, b) (c, d) = (a + c, b + d)

-- | Source and field name to per-line cost, for the language server. An
-- unparseable or un-elaboratable document has no cost to show yet.
profileSource :: String -> String -> [LineCost]
profileSource field source =
  case parseProgram source >>= elaborate field of
    Left _ -> []
    Right e -> lineCosts (elabIr e)