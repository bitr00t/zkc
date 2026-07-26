# zkc — Phase 7, O.2 (recursive composition: one proof attesting to another)

The final increment. O.1 expressed a verifier check — one FRI fold — as a
determinate circuit. O.2 closes the loop: it proves that circuit over a *real*
fold drawn from a *real* inner proof, so the outer proof attests to the inner
one. This is the smallest honest recursion the design asks for, and it carries
the same security test every phase has: a tampered inner claim breaks the outer
proof.

**Prerequisite:** builds on O.1 (the `fri_fold` verifier check) and phase 5 (the
FRI/STARK prover). Apply the earlier drops first. One new file:
`backend/zkc-core/tests/recursion_tests.rs`.

## What it does
1. **Inner proof.** A real FRI proof of a low-degree polynomial is produced and
   verified — the phase-5 proof being recursed over.
2. **A real fold step.** Replaying the transcript recovers the folding
   challenge; from query 0, round 0 it takes the openings f(x) and f(-x), the
   domain point x, and the value the proof *claims* for the next layer. These
   are the inner proof's own numbers, not a reconstruction.
3. **The recursion.** Those values are the witness to the `fri_fold` verifier
   circuit (O.1). Lowered to Plonkish over Goldilocks and proved with the same
   STARK prover, it yields an **outer proof that verifies** — attesting the
   inner proof's fold relation holds.
4. **Security.** Tampering the claimed next-layer value leaves the verifier
   circuit unsatisfied, so an honest prover refuses; and a maliciously forced
   outer proof fails to verify. The phase-0 discipline, one level up.

## Build / test
    cd backend && cargo test -p zkc-core --test recursion_tests   # 2 tests, green
    cargo test -p zkc-core                                          # 52 core-crate tests

## Notes
- **No production code changes.** O.2 uses only the existing public APIs — the
  FRI prover/verifier, the transcript, the STARK prover/verifier, the Plonkish
  lowering, and the witness solver — plus the O.1 verifier circuit. It adds a
  single test file.
- The fold the circuit checks is exactly the prover's own: `verify` computes
  `(f(x)+f(-x))/2 + beta*(f(x)-f(-x))/(2x)`, and so does `fri_fold`.
- **Scope, honestly.** This verifies *one* fold step inside the outer proof — the
  smallest honest recursion. A complete in-circuit FRI verifier (all rounds,
  Merkle openings, the transcript, the final-poly check) is the workstream's
  larger arc and remains future depth; O.2 proves the model end to end on the
  piece that matters.
- With O.2, **phase 7 is complete** — both halves: N (the lowering is verified
  against an executable spec, per-rule and mutation-tested) and O (a verifier in
  the language, and a proof that attests to another).
- Local-only `backend/Cargo.lock` pins remain required (never commit): `zeroize
  1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`, `rayon-core 1.12.1`.
