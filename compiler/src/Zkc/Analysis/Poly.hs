-- | Multivariate polynomials over a prime field.
--
-- The determinacy analysis works by turning every assertion into a
-- polynomial equation @P = 0@ over the circuit's /atoms/ (inputs and advice
-- wires), then asking algebraic questions about it. This module is the
-- arithmetic that makes those questions answerable.
--
-- Representation: a map from monomials to coefficients, where a monomial is
-- a map from atom to exponent. Sparse, canonical (zero coefficients are
-- never stored), and ordered, so equality is structural.
--
-- All arithmetic is modulo a prime supplied by the caller — see "Zkc.Field"
-- for why reasoning over the integers instead would be unsound.
module Zkc.Analysis.Poly
  ( Mono
  , Poly
  , constant
  , var
  , add
  , sub
  , mul
  , neg
  , isZero
  , asConstant
  , atoms
  , substituteZero
  , splitLinear
  , monomialCount
  , isSingleMonomialIn
  , render
  ) where

import Data.List (intercalate, sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | A monomial: atom -> exponent. The empty map is the constant monomial 1.
type Mono = Map.Map Int Int

-- | A polynomial: monomial -> coefficient. Coefficients are kept reduced
-- into @0 .. p-1@ and zero coefficients are never stored.
newtype Poly = Poly (Map.Map Mono Integer)
  deriving (Eq, Ord)

instance Show Poly where
  show = render (\i -> "w" ++ show i)

normalize :: Integer -> Map.Map Mono Integer -> Poly
normalize p = Poly . Map.filter (/= 0) . Map.map (`mod` p)

constant :: Integer -> Integer -> Poly
constant p value = normalize p (Map.singleton Map.empty value)

var :: Integer -> Int -> Poly
var p atom = normalize p (Map.singleton (Map.singleton atom 1) 1)

add :: Integer -> Poly -> Poly -> Poly
add p (Poly a) (Poly b) = normalize p (Map.unionWith (+) a b)

neg :: Integer -> Poly -> Poly
neg p (Poly a) = normalize p (Map.map negate a)

sub :: Integer -> Poly -> Poly -> Poly
sub p a b = add p a (neg p b)

mul :: Integer -> Poly -> Poly -> Poly
mul p (Poly a) (Poly b) = normalize p $ Map.fromListWith (+)
  [ (Map.unionWith (+) ma mb, ca * cb)
  | (ma, ca) <- Map.toList a
  , (mb, cb) <- Map.toList b
  ]

isZero :: Poly -> Bool
isZero (Poly a) = Map.null a

-- | The polynomial's value if it is a constant.
asConstant :: Poly -> Maybe Integer
asConstant (Poly a) = case Map.toList a of
  [] -> Just 0
  [(mono, coeff)] | Map.null mono -> Just coeff
  _ -> Nothing

-- | Every atom occurring in the polynomial.
atoms :: Poly -> Set.Set Int
atoms (Poly a) = Set.unions (map Map.keysSet (Map.keys a))

-- | Substitute @atom := 0@, i.e. drop every monomial mentioning it.
substituteZero :: Int -> Poly -> Poly
substituteZero atom (Poly a) = Poly (Map.filterWithKey (\mono _ -> not (Map.member atom mono)) a)

-- | View the polynomial as @c * atom + r@, where neither @c@ nor @r@
-- mentions @atom@.
--
-- Returns 'Nothing' when the atom occurs with degree 2 or higher, because
-- then the equation is not linear in it and a unique solution does not
-- follow from a nonzero leading coefficient. (@x^2 = 1@ has two roots.)
splitLinear :: Integer -> Int -> Poly -> Maybe (Poly, Poly)
splitLinear p atom (Poly a)
  | any (> 1) degrees = Nothing
  | otherwise = Just (Poly coefficient, Poly remainder)
  where
    degrees = [ d | mono <- Map.keys a, Just d <- [Map.lookup atom mono] ]
    (withAtom, without) = Map.partitionWithKey (\mono _ -> Map.member atom mono) a
    coefficient = Map.filter (/= 0) (Map.map (`mod` p) (Map.mapKeys (Map.delete atom) withAtom))
    remainder = without

monomialCount :: Poly -> Int
monomialCount (Poly a) = Map.size a

-- | True when the polynomial is a single monomial all of whose atoms are in
-- the given set. Used to decide \"this coefficient is nonzero\": a product of
-- values each known to be nonzero is itself nonzero in a field (no zero
-- divisors), which is precisely the property being leaned on.
isSingleMonomialIn :: Set.Set Int -> Poly -> Bool
isSingleMonomialIn nonzeroAtoms (Poly a) = case Map.toList a of
  [(mono, coeff)] -> coeff /= 0 && all (`Set.member` nonzeroAtoms) (Map.keys mono)
  _ -> False

-- | Render for diagnostics, using a caller-supplied name for each atom.
render :: (Int -> String) -> Poly -> String
render nameOf (Poly a)
  | Map.null a = "0"
  | otherwise = intercalate " + " (map term (sortOn fst (Map.toList a)))
  where
    term (mono, coeff)
      | Map.null mono = show coeff
      | coeff == 1 = factors mono
      | otherwise = show coeff ++ "*" ++ factors mono
    factors mono = intercalate "*"
      [ if power == 1 then nameOf atom else nameOf atom ++ "^" ++ show power
      | (atom, power) <- Map.toList mono ]