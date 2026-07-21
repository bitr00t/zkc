-- | Known fields and their moduli.
--
-- The compiler stays generic over the field — circuits name one
-- (@bn254@, @goldilocks@) and the backend instantiates it. But the
-- determinacy analysis has to reason about whether a coefficient is
-- /nonzero/, and that is a question about a specific prime: 21 is nonzero
-- over BN254 and zero over F_21 (were that a field). Reasoning over the
-- integers instead would be unsound, since a coefficient can be a nonzero
-- integer and still vanish modulo p.
--
-- So the frontend keeps a small table of moduli and does its polynomial
-- arithmetic in the right field. Adding a field here is a one-line change;
-- naming an unknown field is a clean error rather than a silent assumption.
module Zkc.Field (fieldModulus, knownFields) where

-- | The scalar field modulus for a named field, if the compiler knows it.
fieldModulus :: String -> Maybe Integer
fieldModulus name = lookup name knownFields

knownFields :: [(String, Integer)]
knownFields =
  [ -- BN254 scalar field (r), what arkworks' Groth16 backend instantiates.
    ("bn254", 21888242871839275222246405745257275088548364400416034343698204186575808495617)
    -- Goldilocks, 2^64 - 2^32 + 1: the FRI/STARK field for phase 5.
  , ("goldilocks", 18446744069414584321)
  ]