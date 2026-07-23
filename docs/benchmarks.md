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

---

# Plonkish — phase 4, Workstream D.1 (baseline)

> Status: the **unoptimised** lowering. One row per arithmetic node, one per
> assertion, no fusion. These numbers are the baseline D.2's gate fusion is
> measured against, exactly as `fuse = false` was for R1CS.

Measured with `lower::<Fr>` and `lower_plonkish::<Fr>` on the same IR:

| circuit | R1CS constraints | Plonkish rows | copy constraints |
|---|---|---|---|
| `relation` | 1 | 3 | 2 |
| `mul_square` | 2 | 3 | 3 |
| `divide` | 2 | 5 | 4 |
| `IsZero` | 2 | 7 | 7 |
| `WideSum` (`z == a+b+..+f`) | 1 | 6 | 5 |
| `ManyMul` (8 products) | 8 | 16 | 8 |

Unfused Plonkish costs **1.5× to 3.5×** what R1CS does, which is the expected
shape of the result and the reason D.2 exists: R1CS gets unlimited linear
terms free, while a naive row-per-node lowering spends a row on every addition
and every constant.

**Fusion closes the gap — except where it structurally cannot.**

| circuit | R1CS | Plonkish baseline | Plonkish fused |
|---|---|---|---|
| `relation` | 1 | 3 | **1** |
| `mul_square` | 2 | 3 | **2** |
| `divide` | 2 | 5 | **2** |
| `IsZero` | 2 | 7 | **2** |
| `ManyMul` (8 products) | 8 | 16 | **8** |
| `WideSum` (`z == a+b+..+f`) | 1 | 6 | **5** |

On every multiplication-shaped circuit the fused Plonkish lowering **matches
R1CS exactly**. `assert x * inv == 1 - out` is four rows unfused — a constant,
a subtraction, a multiplication and the assertion — and one row fused, because
a single gate holds a product, a linear term and a constant at once:

```text
    q_M·x·inv  +  q_O·out  +  q_C  =  0        with q_M = 1, q_O = 1, q_C = -1
```

`WideSum` is the exception, and it is the honest one: fusion takes it from 6
rows to 5 and then stops. Six summands do not fit in three-cell gates however
cleverly they are packed, while R1CS folds them into one linear combination
for free. **This is structural, not a missing optimisation** — and it is
exactly the disagreement that justifies keeping the IR neutral. Neither
arithmetization dominates; which is cheaper depends on the circuit's shape.

**Fusion also removes wiring.** Copy constraints are a cost with no R1CS
counterpart: in R1CS a wire *is* a variable and sharing is free, while in
Plonkish every reuse across rows must be asserted, and a real prover pays for
those in the permutation argument. Folding a value into the gate that consumes
it means it never crosses a row boundary at all — `IsZero` drops from 7 copies
to 2, and `ManyMul` from 8 to **zero**.

**How fusion decides.** Not by pattern-matching. A node is folded into its
consumer while the resulting expression stays inside the three-cell budget;
when it would overflow, the node is *materialised* — given its own row and a
cell — and the consumer refers to it by wire. Materialising is always
available and always fits, which makes the procedure total: materialise
everything and you are back at the baseline. Values used more than once are
materialised up front, for the same reason common-subexpression elimination
exists.

Correctness travels with cost, as in Workstream C: tests check that the fused
circuit accepts the honest witness and rejects a forged output, so the row
count never falls by weakening the circuit.

---

# Cost comparison — phase 4, Workstream F.1

`zkc-stats` lowers an IR both ways and prints the two bills. It is the neutral
IR paying rent: the same graph, two arithmetizations, a per-circuit answer to
which is cheaper.

```bash
cargo build --manifest-path backend/Cargo.toml --bin zkc-stats
backend/target/debug/zkc-stats build/*.ir.json          # human-readable
backend/target/debug/zkc-stats build/*.ir.json --json   # one object per line
```

Measured across the repo's circuits (fused counts):

| circuit | R1CS constraints | Plonkish rows | copies | cheaper |
|---|---|---|---|---|
| `relation` | 1 | 1 | 0 | tie |
| `mul_square` | 2 | 2 | 2 | tie |
| `IsZero` | 2 | 2 | 2 | tie |
| `divide` | 2 | 2 | 1 | tie |
| `ManyMul` (8) | 8 | 8 | 0 | tie |
| `WideSum` | 1 | 5 | 4 | **R1CS** |

The headline is the last column, and specifically that it is not constant.
Fusion brings Plonkish level with R1CS on everything multiplication-shaped;
`WideSum` is the one circuit where R1CS's free linear algebra wins and no gate
fusion can catch up. **Neither arithmetization dominates** — which is the
entire justification for keeping the Core IR arithmetization-agnostic. Had one
always won, the neutrality would have been an expensive gesture; because the
answer is per-circuit, the compiler now has a real decision to make, and F.2
is what lets a user act on it.

The tool reports Plonkish copy constraints as a first-class number because they
are a cost with no R1CS counterpart — a real prover pays for them in the
permutation argument — and fusion drives them down too (`ManyMul` to zero).

---

# Phase 5 — STARK vs the Groth16 baseline

The phase-4 cost model reported constraint and row counts; phase 5 adds the
numbers a proof system is actually judged on. Measured on the `IsZero` circuit,
honest witness — the hand-written FRI-STARK over Goldilocks (with the stand-in
hash, `blowup = 4`, 32 queries) against the borrowed arkworks Groth16 over
BN254:

| | Groth16 (BN254) | zkc STARK (Goldilocks) |
|---|---|---|
| proof size | **128 bytes** | ~25,000 bytes |
| prover time | 21.7 ms | **1.1 ms** |
| verifier time | 58.9 ms | **2.0 ms** |
| trusted setup | required | **none** |
| trust assumption | pairing + toxic waste | a hash |

The trade is exactly the textbook one, and worth stating rather than
editorialising. **Groth16 wins proof size by two orders of magnitude** — a
pairing-based SNARK is constant-size and tiny, and nothing FRI does will match
128 bytes. **The STARK wins setup and speed:** no trusted ceremony, no toxic
waste, only a hash for its cryptography, and on a circuit this small the
absence of a pairing setup and pairing checks makes it far quicker end to end.

Two honest caveats on the numbers. The timings are on a tiny circuit, where
Groth16's fixed pairing costs dominate; at realistic circuit sizes the picture
shifts (Groth16 prover time grows with the circuit, STARK proof size grows
polylogarithmically), and phase 6's profiler is where that curve gets mapped.
And the STARK proof size here is inflated by the stand-in hash's width-1
digests and an unoptimised opening format; a real arithmetic hash and shared
Merkle caps would cut it. The point is not the exact ratio but that the
compiler can now put both systems on the table — the same move phase 4 made for
two arithmetizations, one level down.
