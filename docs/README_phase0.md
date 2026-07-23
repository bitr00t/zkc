# zk-phase0 — the under-constraining spike

Phase 0 of building a Zero-Knowledge circuit compiler from scratch (Haskell
frontend + Rust backend, R1CS skeleton now, own FRI/STARK prover later). The
goal of this phase is **not** compiler code — it is to *own the mental model*
the whole language design rests on: the split between **computing** a value
and **constraining** it, and the vulnerability that opens when you do the
first without the second.

Everything here runs and is tested.

```bash
./scripts/run_all.sh        # build, test, and run both narrated demos
# or:
cargo test                  # 13 core tests + 4 Groth16 tests
```

## What it shows

There are two crates, with deliberately opposite dependency policies.

### `field-r1cs` — zero dependencies

Hand-rolled so the math is yours, not a library's:

- **`field.rs`** — prime-field arithmetic, const-generic over the modulus.
  The same code is instantiated as `F17` (tiny, hand-checkable) and
  `Goldilocks` (`2^64 − 2^32 + 1`, the field FRI/STARK provers use). Add, mul,
  neg, `pow`, Fermat inverse.
- **`r1cs.rs`** — the R1CS representation and a ~30-line satisfiability
  checker: for each row, `(A·w) * (B·w) == (C·w)`. This is the ground truth
  the rest of the spike leans on.
- **`iszero.rs`** — the `IsZero` circuit in two variants (correctly
  constrained vs. under-constrained) with an honest and a malicious witness
  generator.

Run the narrated version:

```
cargo run -p field-r1cs --bin underconstrained_demo
```

It prints two witnesses for the broken circuit that share the input `x = 5`
but disagree on the output (`out = 0` and `out = 1`), both certified
satisfiable by our own checker — the essence of "under-constrained".

### `groth16-demo` — arkworks

The *same* circuit through a real SNARK (Groth16 over BN254), which is the
"borrowed prover" for phases 1–3 of the roadmap:

```
cargo run -p groth16-demo --bin demo_groth16
```

The punchline (act 4): a **cryptographically valid Groth16 proof that
`5 == 0`**, accepted by the verifier — purely because the circuit omits one
constraint. Against the correct circuit the same forged assignment is
unsatisfiable, so the honest prover cannot build a proof at all.

## Why this is the right phase 0

The under-constrained bug is invisible to honest testing (every honest input
passes) and catastrophic in production. That is precisely the bug class the
planned language eliminates by construction: a type system that distinguishes
`Determined` wires from raw `Advice`, so a value that was computed but never
constrained cannot silently become an output. This spike is the concrete,
runnable reference for *what* that type system must rule out — you can point
at `demo_groth16` act 4 and say "this must become a compile error."

## Layout

```
zk-phase0/
├── field-r1cs/          # zero-dependency core
│   ├── src/field.rs         # prime field, const-generic over the modulus
│   ├── src/r1cs.rs          # R1CS + satisfiability checker
│   ├── src/iszero.rs        # the two circuit variants + witnesses
│   ├── src/bin/underconstrained_demo.rs
│   └── tests/core_tests.rs  # field axioms, known vectors, the 2-witness proof
├── groth16-demo/        # arkworks: the same circuits through a real SNARK
│   ├── src/lib.rs           # ConstraintSynthesizer for both variants
│   ├── src/bin/demo_groth16.rs
│   └── tests/groth16_tests.rs
├── scripts/
│   ├── run_all.sh
│   └── field_check.jl   # independent Julia cross-check of the field vectors
├── docs/ROADMAP.md      # where this sits in the full compiler plan
└── rust-toolchain.toml  # pinned to 1.75.0
```

## Notes

- **Cargo.lock is committed** and pins a few transitive crates (`zeroize`,
  `rayon-core`) to versions that build on Rust 1.75; newer releases require a
  newer toolchain. Bump both together when you move the toolchain up.
- The field reduction is plain `%` on a `u128` intermediate — correct and
  clear, but Montgomery/Goldilocks-specific reduction is a phase-5 concern.
- `scripts/field_check.jl` recomputes the Goldilocks test vectors with Julia
  `BigInt` as an independent check; Julia is not a build dependency.

## Next step (phase 1)

Design the surface language's grammar and the typed Core-IR (arithmetization-
agnostic, so it can lower to both R1CS *and* AIR later), then lower it to R1CS
and reuse this arkworks backend to get source-file → proof end to end. See
`docs/ROADMAP.md`.
