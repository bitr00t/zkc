# zkc — Phase 7, N.2 (per-rule faithfulness of the lowering, proved not sampled)

The second increment of Workstream N. Where N.1 gave the IR an executable
meaning and checked both lowerings against it on witnesses, N.2 proves the
lowering *rules*: for each IR operation, the constraints and rows the lowering
emits accept an assignment exactly when the operation's defining relation holds
— for every field element, not a sampled few.

**Prerequisite:** builds on N.1 (`Ir::is_satisfied` / `Ir::unmet`). Apply
`zkc_phase7_n1.zip` first.

## What it proves, and how
The proof is by exhaustion over a tiny field, F_13. Each rule's defining
relation and the polynomials the lowering emits for it have total degree at most
two; a degree-`d` polynomial identity that holds on every point of a field with
more than `d` elements is the zero polynomial, so agreement across all of F_13
(13 > 2) is a *proof* the identity holds over any field, not a sample. This is
the Schwartz–Zippel fact the subject rests on, turned on the compiler.

For each operation the test builds the smallest circuit isolating it — the op
feeding one assertion against a prover-chosen output — instantiates the *real*
lowering over F_13 (everything downstream is generic over `ZkField`), and
enumerates every assignment of the free wires. At each point three things must
hold: the IR spec, the R1CS lowering, and the Plonkish lowering all agree, and
their shared verdict equals `out == op(args)` computed independently. Because the
output ranges over the whole field, the forgery direction (`out ≠ op(args)`) is
covered as thoroughly as the honest one — the rule is pinned from both sides,
and in both fusion modes.

Rules covered: `const`, `add`, `sub`, `mul`, `neg`, and the equality assertion.
A `the_check_sees_both_acceptance_and_rejection` test guards against a vacuous
pass by confirming both verdicts actually occur.

## Build / test
    cd backend && cargo test -p zkc-core --test lowering_faithfulness_tests
    # 7 tests, all green

## Notes
- **No production code changes.** N.2 is a verification workstream: it proves the
  *existing* lowering faithful, adding only a proof (one new test file). The IR,
  both lowerings, the witness solver, and the determinacy analysis are untouched.
- The tiny field `Fp<P>` lives in the test and implements `ZkField`, so the real
  `lower_with` / `lower_plonkish_with` run over it unchanged — the thing verified
  is the shipping lowering, not a model of it.
- Local-only `backend/Cargo.lock` pins remain required (never commit): `zeroize
  1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`, `rayon-core 1.12.1`.
- Next: N.3 (a mutation harness that corrupts each rule and confirms this check
  catches it — evidence the specification can fail), then O (a verifier in the
  language, and recursion).
