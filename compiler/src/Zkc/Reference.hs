-- | A generated reference for a gadget library (phase 6, M.2).
--
-- Every line is derived from a gadget's determinacy *summary* — the same
-- record the compositional proof produces and caches — so the documentation
-- states exactly what the compiler proved: the signature, the case split the
-- proof rested on, and any nonzero facts the gadget requires of its caller or
-- guarantees in return. It is generated, never hand-written, so it cannot fall
-- out of step with the code.
module Zkc.Reference
  ( renderReference
  , referenceFor
  ) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map

import Zkc.Analysis.Determinacy (Assumption(..), Summary(..))
import Zkc.Syntax.Ast (GadgetDef(..))

-- | The whole library's reference, one section per gadget.
renderReference :: [(GadgetDef, Summary)] -> String
renderReference gadgets =
  intercalate "\n" (header : map (uncurry referenceFor) gadgets)
  where
    header =
      "# Gadget reference\n\n\
      \Generated from determinacy summaries: each entry states what the \
      \compiler proved, not a hand-written description.\n"

-- | One gadget's reference block.
referenceFor :: GadgetDef -> Summary -> String
referenceFor def summary = unlines $
  [ "## " ++ gdName def
  , ""
  , "    " ++ signature
  , ""
  , "- inputs: " ++ inputs
  , "- outputs: " ++ outputs
  ]
  ++ [ determinedLine ]
  ++ factLines
  where
    signature =
      gdName def ++ "(" ++ commas (gdParams def) ++ ") -> ("
      ++ commas (gdResults def) ++ ")"
    inputs  = if null (gdParams def)  then "(none)" else commas (gdParams def)
    outputs = if null (gdResults def) then "(none)" else commas (gdResults def)

    -- Local param/result wires back to the names the caller sees, so the case
    -- split reads in the gadget's own vocabulary.
    nameMap = Map.fromList
      (  zip (sumParamWires summary)  (gdParams def)
      ++ zip (sumResultWires summary) (gdResults def) )
    nameOf w = Map.findWithDefault ("wire" ++ show w) w nameMap

    determinedLine = case sumBranches summary of
      [[]] -> "- determined: directly, with no case split"
      brs  -> "- determined by cases: " ++ intercalate "; " (map renderCase brs)
    renderCase [] = "otherwise"
    renderCase as = intercalate " and " (map renderAssump as)
    renderAssump (AssumeZero w)    = nameOf w ++ " == 0"
    renderAssump (AssumeNonZero w) = nameOf w ++ " != 0"

    factLines =
      [ "- requires: " ++ commas (paramNames (sumRequired summary)) ++ " != 0"
      | not (null (sumRequired summary)) ]
      ++
      [ "- guarantees: " ++ commas (paramNames (sumNonzero summary)) ++ " != 0"
      | not (null (sumNonzero summary)) ]
    paramNames idxs = [ gdParams def !! i | i <- idxs, i < length (gdParams def) ]

    commas = intercalate ", "
