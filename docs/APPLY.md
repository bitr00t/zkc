# zkc — Phase 7, begin (N.1: the executable IR specification)

Phase 7 is the roadmap's last: **recursion and formal verification of the
lowering.** This drop opens it — the full design note (`docs/phase7.md`) plus the
first workstream increment, N.1.

## The design (docs/phase7.md)
Phase 7 has two halves. **N — formal verification of the lowering:** the
IR→R1CS/Plonkish lowering has been differential-tested since phase 4 (the two
arithmetizations agree with *each other*), but never against an independent
statement of what the IR *means* — so two lowerings wrong in the same way would
agree. **O — recursion:** make "this proof verifies" a circuit a proof can
assert. Order N → O; within N, N.1 (a spec) → N.2 (per-rule proofs) → N.3 (a
mutation harness proving the spec can fail).

## N.1 — An executable IR specification (this drop)
`Ir::is_satisfied` / `Ir::unmet` (in `backend/zkc-core/src/ir.rs`) fix the
meaning of the IR against a complete wire assignment, naming no arithmetization:
the constant-one wire is 1, every arithmetic node equals its operation on its
arguments, every assertion holds, and a *hint* node is unconstrained (the
prover's freedom the determinacy system disciplines). It returns the list of
`Unmet` obligations, empty when the assignment is a model.

This is the third party the differential test lacked. New tests
(`backend/zkc-core/tests/core_tests.rs`, phase-7 section) pin all three together:
- `spec_agrees_with_both_lowerings_on_honest_witnesses` — spec ⟺ R1CS ⟺ Plonkish.
- `spec_independently_rejects_the_forgery` — the spec names the unmet
  `(x * out) == 0` assertion on the phase-0 attack, with no lowering consulted.
- `spec_matches_both_lowerings_under_random_perturbation` — 300 random atom
  assignments per fixture, re-solved, all three agree.
- `spec_has_teeth_it_pins_a_node_equation_r1cs_does_not_read` — corrupting an
  intermediate sum slips past R1CS (which folds the linear chain) but the spec
  catches it, proving the oracle is independent, not a restatement of R1CS.

## Build / test
    cd backend && cargo test -p zkc-core        # 49 core tests (was 45), all green

## Notes
- Additive and generic over `ZkField`; determinacy, SMT, witness solving, and
  both lowerings are unchanged, and the phase-0 forgery is still rejected.
- The two `unused import` warnings under `cargo test` are pre-existing in
  `goldilocks_tests.rs` (phase 5), untouched here.
- Local-only `backend/Cargo.lock` pins remain required to build (never commit):
  `zeroize 1.8.1`, `zeroize_derive 1.4.2`, and for the arkworks path
  `rayon 1.7.0` + `rayon-core 1.12.1` (rayon-core >=1.13 needs rustc >=1.80).
- Next: N.2 (per-rule faithfulness via the SMT layer or exhaustion) and N.3
  (the mutation harness), then O (a verifier in the language, and recursion).
