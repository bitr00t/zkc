# zkc — Phase 7, O: in-circuit Fiat-Shamir

The self-contained verifier. The complete in-circuit FRI verifier trusted its
fold challenge as an input; this derives it *in-circuit* from the layer
commitment, exactly as the transcript does — so a prover cannot pick the
challenge after committing, which is the whole point of Fiat-Shamir.

**Prerequisite:** builds on the in-circuit FRI verifier drop (`hash_leaf`,
`compress`, `fri_verify_full`). Supersedes that drop's `compiler/tests/Spec.hs`
and `backend/zkc-core/tests/fri_verifier_tests.rs`.

## The challenge, in the field
The transcript draws a challenge as a hash of everything committed so far. With
the circuit-friendly hash and the transcript state `[seed, root]` (domain
separator, then the layer commitment), the round-0 folding challenge is
`sbox(seed + root + 6)`, `sbox(x) = x^7`. That collapses to a single gadget:
- `std/fs_challenge.zkc` — `fs_challenge(seed, root) -> (alpha)`, `alpha = sbox(seed + root + 6)`.

The backend test derives `alpha` this way and checks it against the *real*
transcript (`assert_eq!(alpha_derived, transcript.challenge())`) before proving,
so the in-circuit derivation is bit-for-bit the transcript's.

## The verifier: examples/fri_verify_fs.zkc
The complete verifier, but `alpha` is no longer an input — it is
`(alpha) = fs_challenge(seed, root)`, then fed to the fold. Everything else (the
two Merkle-path checks, the fold, the final-codeword check) is unchanged. The
circuit proves determinate: `alpha`, like every other wire, is determined — here
by the commitment, not by the prover.

## Held honest end to end
- Frontend (`compiler/tests/Spec.hs`): `fs_challenge` proves determinate and its
  under-constrained fixture is rejected; the Fiat-Shamir verifier proves
  determinate with all five includes resolved.
- Backend (`fri_verifier_tests.rs`): the derived challenge matches the real
  transcript; the verifier proves and verifies as an outer STARK proof; and a
  challenge *not* equal to `fs_challenge(seed, root)` is rejected — a prover
  cannot substitute a convenient one.

## Build / test
    make -C compiler all && cd compiler && ghc -O0 -isrc -itests \
        -outputdir build/test-objs -o build/spec tests/Spec.hs && ./build/spec   # 154/154
    cd backend && cargo test -p zkc-core --test fri_verifier_tests               # 4 green

## Notes
- Additive: language, determinacy, SMT, both lowerings, the witness solver, and
  the phase-5 prover/transcript are unchanged; only a gadget and tests are added.
- **Scope, honestly.** The *fold challenge* is now derived in-circuit — the
  security-critical Fiat-Shamir value for FRI. The *query index* is still an
  input: the transcript derives it by folding the challenge's decimal digits,
  which is not an algebraic function of the field element. Deriving the index
  in-circuit needs a circuit-friendly (bit-mask) index extraction in the
  transcript — a small, separate change to `challenge_index`.
- Local-only `backend/Cargo.lock` pins remain required (never commit): `zeroize
  1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`, `rayon-core 1.12.1`.
