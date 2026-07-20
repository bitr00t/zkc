-- | Core IR optimization passes.
--
-- Three classic passes, run in one forward sweep plus a cleanup:
--
--   1. constant folding — evaluate operations whose operands are constants;
--   2. common subexpression elimination — share structurally identical nodes;
--   3. dead code elimination — drop nodes no assertion depends on.
--
-- Folding produces plain 'Integer' constants and may go negative: the IR
-- stays field-agnostic, and the backend reduces modulo whichever prime it
-- instantiates. Hints are never folded or shared — a hint is an effect
-- (\"ask the witness generator\"), and silently merging two of them would
-- change which values the prover is free to choose.
module Zkc.Core.Passes (optimize, Stats(..), renderStats) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Zkc.Core.Ir

data Stats = Stats
  { statsFolded :: Int
  , statsShared :: Int
  , statsDropped :: Int
  } deriving (Eq, Show)

renderStats :: Stats -> String
renderStats s =
  "folded " ++ show (statsFolded s)
  ++ ", shared " ++ show (statsShared s)
  ++ ", dropped " ++ show (statsDropped s)

data Acc = Acc
  { accNext :: WireId
  , accSubst :: Map.Map WireId WireId    -- ^ old wire -> canonical new wire
  , accMemo :: Map.Map Op WireId         -- ^ CSE table
  , accConsts :: Map.Map WireId Integer
  , accNodes :: [Node]                   -- ^ reversed
  , accFolded :: Int
  , accShared :: Int
  }

optimize :: Ir -> (Ir, Stats)
optimize ir = (renumber ir', stats)
  where
    inputWires = map iiWire (irInputs ir)
    acc0 = Acc
      { accNext = 1 + length inputWires
      , accSubst = Map.fromList [ (w, w) | w <- constOneWire : inputWires ]
      , accMemo = Map.empty
      , accConsts = Map.empty
      , accNodes = []
      , accFolded = 0
      , accShared = 0
      }
    accEnd = foldl step acc0 (irNodes ir)
    resolve w = Map.findWithDefault w w (accSubst accEnd)
    asserts' = [ a { aLhs = resolve (aLhs a), aRhs = resolve (aRhs a) }
               | a <- irAssertions ir ]
    kept = reverse (accNodes accEnd)
    (live, droppedCount) = eliminateDead kept asserts'
    ir' = ir { irNodes = live, irAssertions = asserts' }
    stats = Stats
      { statsFolded = accFolded accEnd
      , statsShared = accShared accEnd
      , statsDropped = droppedCount
      }

step :: Acc -> Node -> Acc
step acc (Node oldWire op0) =
  let op = mapArgs (\w -> Map.findWithDefault w w (accSubst acc)) op0
  in case constFold acc op of
       Just value -> emitConst acc oldWire value
       Nothing -> case Map.lookup op (accMemo acc) of
         Just existing | not (isHint op) ->
           acc { accSubst = Map.insert oldWire existing (accSubst acc)
               , accShared = accShared acc + 1 }
         _ -> emitNode acc oldWire op

mapArgs :: (WireId -> WireId) -> Op -> Op
mapArgs f op = case op of
  OConst n   -> OConst n
  OAdd a b   -> OAdd (f a) (f b)
  OSub a b   -> OSub (f a) (f b)
  OMul a b   -> OMul (f a) (f b)
  ONeg a     -> ONeg (f a)
  OHint k n as -> OHint k n (map f as)

-- | Fold when every operand is a known constant. Hints never fold.
constFold :: Acc -> Op -> Maybe Integer
constFold acc op = case op of
  OConst n -> Just n
  OAdd a b -> (+) <$> known a <*> known b
  OSub a b -> (-) <$> known a <*> known b
  OMul a b -> (*) <$> known a <*> known b
  ONeg a   -> negate <$> known a
  OHint _ _ _ -> Nothing
  where
    known w = Map.lookup w (accConsts acc)

emitConst :: Acc -> WireId -> Integer -> Acc
emitConst acc oldWire value =
  case Map.lookup (OConst value) (accMemo acc) of
    Just existing ->
      acc { accSubst = Map.insert oldWire existing (accSubst acc)
          , accShared = accShared acc + 1 }
    Nothing ->
      let wire = accNext acc
      in acc { accNext = wire + 1
             , accSubst = Map.insert oldWire wire (accSubst acc)
             , accMemo = Map.insert (OConst value) wire (accMemo acc)
             , accConsts = Map.insert wire value (accConsts acc)
             , accNodes = Node wire (OConst value) : accNodes acc
             , accFolded = accFolded acc + 1 }

emitNode :: Acc -> WireId -> Op -> Acc
emitNode acc oldWire op =
  let wire = accNext acc
  in acc { accNext = wire + 1
         , accSubst = Map.insert oldWire wire (accSubst acc)
         , accMemo = Map.insert op wire (accMemo acc)
         , accNodes = Node wire op : accNodes acc }

-- | Keep only nodes some assertion transitively depends on.
eliminateDead :: [Node] -> [Assertion] -> ([Node], Int)
eliminateDead nodes asserts = (live, length nodes - length live)
  where
    nodeMap = Map.fromList [ (nWire n, nOp n) | n <- nodes ]
    roots = concat [ [aLhs a, aRhs a] | a <- asserts ]
    needed = go Set.empty roots
    go seen [] = seen
    go seen (w:ws)
      | w `Set.member` seen = go seen ws
      | otherwise = case Map.lookup w nodeMap of
          Nothing -> go (Set.insert w seen) ws
          Just op -> go (Set.insert w seen) (opArgs op ++ ws)
    live = [ n | n <- nodes, nWire n `Set.member` needed ]

-- | Compact wire ids so they stay dense and topologically ordered, which the
-- backend's validator relies on.
renumber :: Ir -> Ir
renumber ir = ir { irNodes = newNodes, irAssertions = newAsserts }
  where
    base = 1 + length (irInputs ir)
    remap = Map.fromList $
      [ (constOneWire, constOneWire) ]
      ++ [ (iiWire i, iiWire i) | i <- irInputs ir ]
      ++ zip (map nWire (irNodes ir)) [base ..]
    fix w = Map.findWithDefault w w remap
    newNodes = [ Node (fix (nWire n)) (mapArgs fix (nOp n)) | n <- irNodes ir ]
    newAsserts = [ a { aLhs = fix (aLhs a), aRhs = fix (aRhs a) } | a <- irAssertions ir ]