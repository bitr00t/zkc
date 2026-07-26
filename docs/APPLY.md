# zkc — Phase 7, N.3 (a mutation harness: proof the checker has teeth)

The third and final increment of Workstream N. N.1 gave the IR an executable
meaning; N.2 proved the lowering rules faithful to it, exhaustively over a tiny
field. N.3 proves the *check itself* is not vacuous: it deliberately breaks each
lowering rule and confirms the N.1/N.2 verification catches the break.

**Prerequisite:** builds on N.2 — this file *supersedes* the N.2 drop's
`backend/zkc-core/tests/lowering_faithfulness_tests.rs` (it adds the N.3 section
below the N.2 proofs). Apply `zkc_phase7_n1.zip` and `zkc_phase7_n2.zip` first.

## The argument, made concrete
N.2 established that the real lowering agrees with the spec on every assignment.
It follows that *any* corruption of the lowering that changes its behaviour must
disagree with the spec somewhere — so the check would catch it. N.3 turns that
into a live, self-checking property rather than a paper argument.

The harness generates labelled corruptions of each lowered rule — drop / neutralise
a constraint, shift a constraint by a constant, perturb a coefficient, bump or
flip a gate selector, and route a bogus copy constraint — and, over all of F_13,
asserts the **anti-vacuity invariant**: every mutation that changes behaviour
(differs from the honest lowering) is caught by the spec, and at least one such
mutation exists per rule, so the check never passes on nothing. Named tests pin
the design's examples directly: dropping the constraint admits a forgery the spec
rejects; flipping the product selector diverges from the spec; a bogus copy
rejects honest witnesses. A baseline test confirms the unmutated lowering is
never flagged (no false positives).

This is a lasting regression guard: weaken the spec or the check later and a
previously-caught mutation would survive, breaking N.3.

## Build / test
    cd backend && cargo test -p zkc-core --test lowering_faithfulness_tests
    # 12 tests (7 from N.2, 5 from N.3), all green

## Notes
- **No production code changes.** Like N.2, N.3 adds only tests; it corrupts
  *clones* of the lowered structures (all `Clone`, all public) and never touches
  the shipping lowering.
- One subtlety handled: dropping a Plonkish row is done by neutralising its gate
  (zeroing the selectors), not removing it, so the copy and public-cell indices
  that reference rows by position stay valid.
- With N.3, **workstream N (formal verification of the lowering) is complete.**
  Phase 7's remaining half is O — a verifier expressed in the language, and the
  first recursion.
- Local-only `backend/Cargo.lock` pins remain required (never commit): `zeroize
  1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`, `rayon-core 1.12.1`.
