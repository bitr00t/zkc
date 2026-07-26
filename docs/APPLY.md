# zkc — Phase 7, O: the query index, and the boundary of determinacy

The follow-on to in-circuit Fiat-Shamir. The fold challenge is now derived
in-circuit; the query index is the other Fiat-Shamir value. This drop makes the
backend's index derivation honest and algebraic, and records — with proof — why
the *in-circuit* index derivation cannot yet be done soundly.

**Prerequisite:** builds on the in-circuit Fiat-Shamir drop. Supersedes that
drop's `compiler/tests/Spec.hs`.

## The backend, made algebraic
`transcript.rs`: `challenge_index` used to fold the challenge's decimal digits —
deterministic but not an algebraic function of the field element. It now derives
`challenge mod domain`: the low bits of the canonical representative, the value
an in-circuit derivation would have to reproduce. Prove and verify stay in
lockstep, so the round trip is unchanged; the index is now a genuine reduction of
the challenge. (`the_query_index_is_an_algebraic_reduction_of_the_challenge`.)

## The boundary, made concrete
The natural in-circuit binding — `challenge == index + domain*high`, index bits
constrained — **proves determinate** but is **unsound**: `high` is free, so the
prover can hit any index via `high = (challenge - index)/domain`.
- `examples/index_from_challenge.zkc` — proved determinate (frontend
  `indexBindingCase`).
- `naive_index_binding_is_determinate_but_unsound` (backend) — every index in
  `{0,1,2,3}` satisfies it.

The lesson: determinacy rules out under-constrained *outputs*; it does not
certify that an output equals a *canonical reduction*. That is a range property.

## What's needed next
A **decomposition hint** — advice `bits(x, n)` giving x's low bits with the
constraints that reconstruct it — would let `high` be range-checked and make the
derivation sound. Its determinacy needs the SMT-backed checker (as `is_equal`
does). See `docs/in-circuit-index.md` for the full account.

## Build / test
    cd backend && cargo test -p zkc-core --test index_binding_tests   # 2 green
    cargo test -p zkc-core                                            # full suite green
    cd ../compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec                  # 155/155

## Notes
- The backend change is behaviour-preserving for FRI (prove/verify lockstep);
  the commitment test's only assertion (indices land in range) still holds.
- Test progression: frontend 154 -> 155; backend 117 -> 119.
- Local-only `backend/Cargo.lock` pins remain required (never commit): `zeroize
  1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`, `rayon-core 1.12.1`.
