# Constraint-count benchmarks — phase 3, Workstream C

> Status: **C.1 done** (fusion + measured win). **C.2 partial**: the harness and
> a frontend-to-backend benchmark are in place; the SHA-256 / Merkle circuits
> and the Circom comparison are blocked on the gadget stdlib (see the gap at the
> end) and are not yet run.

Prover cost is dominated by **R1CS constraint count**, not IR node count. This
document defines what we measure, records the fusion result, and specifies the
Circom comparison the full benchmark will run.

## What fusion does

The most common shape in a real circuit is `assert a * b == c`. Lowered naively
it costs **two** rank-1 constraints — `a * b = v` for the multiplication, then
`(v − c) · 1 = 0` for the assertion. R1CS expresses it natively in **one**:
`a * b = c`. When a `mul` wire feeds exactly one assertion and nothing else, its
intermediate variable is pure overhead; the lowering (`backend/zkc-core/src/lower.rs`)
skips it and emits the fused constraint directly.

The fusion lives in the R1CS lowering, deliberately, not in the neutral IR
passes: that `a * b == c` collapses to one rank-1 constraint is an R1CS fact,
and a future AIR backend would pack differently from the same IR. Keeping it out
of `Passes.hs` preserves the arithmetization-neutrality invariant.

## What we measure

Two structural numbers from the lowered `R1cs`, before any proving:

- **constraints** — `r1cs.constraints.len()`, the prover's dominant cost.
- **variables** — `r1cs.num_vars`, which fusion also reduces (one per folded mul).

They are structural, so they are deterministic and diff cleanly across runs. The
benchmark reports them for the fused lowering and for `fuse = false` (the exact
phase-2 lowering), so the win is a measured delta, never an assertion.

## Result

Two benchmarks are pinned as tests in `backend/zkc-core/tests/core_tests.rs`.

**Synthetic, `N` independent products** (`benchmark_fusion_halves_constraints…`):

```
BENCH circuit=ManyProducts n=64 constraints_unfused=128 constraints_fused=64 \
      vars_unfused=257 vars_fused=193 reduction=0.50
```

Exactly `2N → N`: a 50% constraint reduction, and `N` fewer variables.

**End-to-end, through the real compiler** (`benchmark_end_to_end…`): the circuit
`benchmarks/many_mul.zkc` is written with a reused Workstream-A gadget
(`product`, proved determined once, compositionally), compiled by the frontend
to `benchmarks/many_mul.json`, then lowered by the backend. Eight products lower
to **8 fused constraints instead of 16** — Workstream A (reuse) and Workstream C
(fusion) working together on IR the frontend actually emitted.

Reproduce:

```bash
# frontend: gadget proved once, IR emitted
compiler/build/zkc build benchmarks/many_mul.zkc -o benchmarks/many_mul.json --explain
# backend: the measured win, both benchmarks
cargo test --manifest-path backend/Cargo.toml -p zkc-core benchmark -- --nocapture
```

Correctness travels with cost: `fusion_preserves_satisfaction_and_still_catches_a_lie`
checks that both lowerings accept the honest witness and reject a forged output,
so the constraint count never shrinks by breaking soundness — the one bug this
project exists to prevent.

## The Circom comparison (specified, not yet run)

The roadmap's target is a like-for-like comparison against Circom on **SHA-256**
and **Merkle inclusion**:

- **Metric**: R1CS constraint count for the same statement. Circom's own
  `--r1cs` reports it; compare against ours from the same inputs.
- **Differential correctness**: the same statement and witness must verify under
  both toolchains. A constraint-count win that changed the circuit's meaning
  would show up here as a verification that disagrees.
- **Fusion on vs off**: report both, so the contribution attributable to fusion
  is isolated from the frontend's own structure.

## The gap, stated plainly

Two things stand between here and the full Circom comparison, and neither is
hidden:

1. **The gadget standard library does not exist yet.** SHA-256 and Merkle need
   `poseidon` / `compress`, boolean decomposition and range checks — and those
   need a gadget to take another gadget's result as an *intermediate* value fed
   into further computation. Workstream A currently binds results to declared
   outputs or to advice-computed wires; the fresh-intermediate case touches the
   Rust witness solver and the IR schema and is the next follow-up. Until it
   lands, the multiplication-heavy benchmark here stands in for those circuits —
   it exercises the same fusion on the same constraint shape.
2. **Circom is not run in this environment.** The methodology above is what the
   comparison will follow; the numbers against Circom are pending the circuits
   from (1).

What is done and measured: the fusion itself, its correctness, and its win —
50% on the constraint shape that dominates real circuits, end to end through the
actual compiler.
