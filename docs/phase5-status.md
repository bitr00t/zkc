# Phase 5 — status

*Own prover: a hand-written FRI/STARK over Goldilocks, replacing arkworks.*

This is the closing report for phase 5. It records what was built, the one
measurement that shaped the whole phase, the findings the tests turned up, and
the single boundary left explicit. The design rationale lives in `phase5.md`;
this is the account of what actually landed.

## The result in one line

A circuit lowered by the unchanged phase-1–4 frontend can now be proved by a
prover written entirely in-house — own field, own FFT, own commitment, own FRI,
own STARK — with no arkworks in the proving path and only a hash for
cryptography. An honest witness proves and verifies; the phase-0 forgery does
not; and a broken wire does not.

## What shaped the phase: the leaf measurement

Before any code, one thing was checked, because it decided the whole shape of
the work. The backend has been generic over `ZkField` since phase 1. If that
genericity were real, a STARK's small field could be slid underneath the
existing lowerings without touching them; if it were only nominal, phase 5
would be a rewrite.

Instantiating the existing R1CS and Plonkish lowerings over the hand-written
Goldilocks field produced **identical constraint counts to BN254**. So the
frontend, both lowerings, the witness solver and the checkers were already
field-agnostic in fact. Phase 5 added a field and a prover *beneath* them and
changed none of them — the new work is a leaf, as the design note claimed and
the measurement confirmed.

## What was built

**Workstream G — the field and the FFT.**
- `goldilocks.rs`: a `ZkField` over a reduced `u64` with the special-form
  reduction (`2^64 ≡ 2^32 - 1`, no division), Fermat inversion, `pow`.
  Differentially tested against an independent arkworks Goldilocks on 50,000+
  random inputs per operation, hardest inputs near `p` and products near
  `(p-1)²`. Reference is test-only.
- `fft.rs` + a `TwoAdicField` trait: iterative NTT/iNTT and a coset LDE, generic
  over the trait. Pinned by the properties that define an FFT — root order,
  round-trip, agreement with naive evaluation, LDE preserves the polynomial.

**Workstream H — commitment and transcript.**
- `hash.rs`: a `Hasher` trait, so nothing below names a concrete hash.
- `merkle.rs`: a Merkle commitment with checkable openings; tested by rejecting
  a forged leaf, a corrupted sibling, and a leaf claimed at the wrong index.
- `transcript.rs`: a Fiat–Shamir transcript; tested on the property soundness
  rests on — changing any absorbed message (value, order, or domain separator)
  changes every subsequent challenge.

**Workstream I — the STARK.**
- `air.rs`: the Plonkish gate identity becomes a polynomial `C` that vanishes on
  the trace domain iff every gate holds; the copy constraints become a
  permutation `σ`. Verified that on an honest witness the quotient `C/Z_H` is a
  polynomial and `Q·Z_H = C`.
- `fri.rs`: the low-degree test — folding, per-layer Merkle commitment, a query
  phase checking the fold chain and openings. Honest low-degree passes; a
  high-degree function is rejected.
- `stark.rs`: commits the trace, folds gate and permutation constraints into one
  composite quotient, FRI-proves it, and checks consistency at the queried
  points. Fiat–Shamir throughout.

## Findings the tests turned up

Two, both from tests doing their job rather than confirming a hope.

**A verifier that under-counted queries.** A property test proving a valid
proof under a mismatched config found that the verifier looped over the proof's
queries without checking there were as many as the security parameter demanded
— a prover could supply fewer and weaken soundness. Fixed: the proof must carry
exactly the configured number of FRI queries.

**The equivalence-of-arithmetizations lesson, reused.** The permutation
argument's wiring test needed a trace that satisfies the gates but violates a
copy constraint. Constructing it made concrete, again, that computed cells are
not free variables — the honest witness solver is the arbiter of intermediate
values, and a meaningful violation has to be crafted at the level of raw trace
cells, which is exactly what `prove_with_trace` exists to allow.

## The wiring hardening

The first cut of workstream I enforced the gate constraint and left the
permutation argument as data. This report covers closing that: a PLONK-style
grand-product argument now commits a column `Z` alongside the trace, and two
constraints force every `σ`-cycle to hold one value. The test that matters
builds a circuit with no gates (all selectors zero) but a wired pair of cells,
and confirms a trace putting different values in them is rejected — the case
the gate constraint alone accepts. Wiring soundness is now enforced, not
represented.

## The one boundary left explicit

FRI here proves the composite *quotient* is low-degree. The committed trace and
`Z` columns are opened for the consistency check but not themselves folded into
the low-degree test (the standard DEEP/FRI-batch step). This is the remaining
hardening for full arithmetic soundness against a prover who commits
non-polynomial columns; it does not affect the honest, forgery, or wiring
results. It is marked here rather than buried, in the same spirit as phase 3's
cvc5 finite-field limitation and workstream C.2's honest partial.

## Cost, measured

On `IsZero`, honest witness — the STARK against the borrowed Groth16:

| | Groth16 (BN254) | zkc STARK (Goldilocks) |
|---|---|---|
| proof size | 128 bytes | ~25,000 bytes |
| prover time | 21.7 ms | 1.1 ms |
| verifier time | 58.9 ms | 2.0 ms |
| trusted setup | required | none |

The textbook trade: Groth16 keeps a two-orders-of-magnitude edge in proof size;
the STARK needs no trusted setup, trusts only a hash, and is faster on a circuit
this small. The compiler can now put both on the table — phase 4's move, one
level down. (Caveats in `benchmarks.md`: tiny-circuit timings favour the STARK,
and its proof size is inflated by the stand-in hash and an unoptimised opening
format.)

## Tests and invariants

- 81 backend tests green, zero warnings.
- Frontend untouched across all of phase 5: 0 `.hs` files changed, 90/90
  frontend checks pass.
- Toolchain note: the arkworks-bearing `zkc-prove` needs lockfile downgrades
  for cargo 1.75 (`rayon`, `zeroize`, `zeroize_derive`); these are applied
  locally for building and measurement and are **not** in the deliverables —
  the committed pins are untouched.

## What "done" looked like, checked

1. Hand-written Goldilocks passing a differential test, implementing `ZkField`
   with the rest of the compiler unchanged. ✓
2. FFT/LDE with round-trip and known-answer properties. ✓
3. Merkle commitment and Fiat–Shamir transcript, each with a tamper test. ✓
4. FRI prover and verifier: honest witness proves and verifies, phase-0 forgery
   does not. ✓
5. arkworks removed from the proving path, present only as a test oracle. ✓
6. Proof-size and timing numbers alongside the Groth16 baseline. ✓
7. Not one line of the frontend changed. ✓

Plus the wiring hardening: the permutation argument enforces the copy
constraints, with a test that a broken wire is rejected. ✓

## What is genuinely left

- **DEEP/FRI-batch** binding the trace and `Z` to low degree — the one boundary
  above.
- **A reviewed hash** (Poseidon or Rescue over Goldilocks) swapped in for the
  stand-in `ToyHash` — a leaf change, by construction, since everything is
  written against the `Hasher` trait.

Neither is a redesign; both are the kind of finishing the roadmap's later
phases were always meant to carry.
