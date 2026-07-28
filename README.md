# zkc

A zero-knowledge circuit compiler, written from scratch, whose thesis is a
**determinacy type system**: a circuit whose outputs are not uniquely determined
by its inputs is a *compile error*, not a runtime surprise.

Under-constrained circuits are the classic catastrophic ZK bug. A constraint
system can be satisfiable by two different witnesses that agree on every input
and disagree on an output — and when that happens, the prover picks whichever
one it prefers and proves it. The circuit is not wrong in a way any test would
show; it is wrong in a way only the attacker notices. zkc treats that as a type
error and refuses to compile.

Frontend in Haskell, backend in Rust. No proving library in the proving path:
own field, own FFT, own commitment, own FRI, own STARK, with a hash as the only
cryptographic assumption.

---

## The idea in one file

```rust
// out = 1 if x == 0, else 0 — the classic gadget.
gadget is_zero(x: field) -> (out: field) {
    // `inv` cannot be computed by the constraint system, only guessed by the
    // prover. So it is `advice`, legal only inside a gadget: the author saying
    // "I know this is subtle, and I claim the assertions below pin it down."
    advice inv = inv_or_zero(x);

    assert x * inv == 1 - out;
    assert x * out == 0;
}

circuit IsZero {
    private x: field;
    output out: field;

    (out) = is_zero(x);
}
```

```
$ zkc build examples/iszero.zkc -o build/iszero.ir.json --explain
compiled 'IsZero' over bn254: 2 inputs, 6 nodes, 2 assertions
  determinacy: 1 output(s) proved determined (out), 2 case(s)
    case x == 0
    case x != 0
```

The proof is a case split the compiler found itself: `x == 0` forces `out = 1`
by the first assertion, `x != 0` makes `x` invertible and the second forces
`out = 0`. Gadgets are proved once and every instantiation reuses the result.

Now take the constraint away and ask for a square root:

```
$ zkc build root.zkc -o /dev/null --smt-solver z3 --smt-dialect int
error: 'root' is under-constrained — the solver constructed a forgery
  --> root.zkc:1
     |
   1 | gadget root(x: field) -> (out: field) {
     |
     = two witnesses satisfy every constraint and agree on all inputs:
     =     x = 4
     = but disagree on:
     =     out = 2   vs   out = -2
     = the prover picks whichever it prefers, and proves it
help: add a constraint that rules out one of these two witnesses
```

The diagnostic is not "this looks risky". It is a counterexample — the actual
forgery, with the values. (That one needed a solver: the decidable core stalls
on it, and stalling is reported as stalling — *"this is not a claim that the
circuit is wrong: the analysis ran out of room before it could decide either
way"* — never as approval.)

**How it works.** Determinacy is uniqueness, and uniqueness is a
self-composition question: *can two assignments satisfy every constraint, agree
on all inputs, and differ on an output?* Most circuits are settled by a decidable
core over polynomial ideals, with case splits on whether an atom is zero. What
the core cannot settle is escalated to an SMT solver, which can refute as well as
prove — and a refutation is the counterexample above.

---

## Three things the project found out

A compiler is only as interesting as what it discovers. Three findings, each
with its tests still in the suite:

**Determinacy does not imply soundness, and here is the circuit that proves it.**
The natural in-circuit derivation of a FRI query index, `challenge == index +
domain*high`, is *proved determinate* — `index` really is a function of the
inputs — and is nevertheless forgeable, because `high` is free and the prover
reaches any index it likes via `high = (challenge - index)/domain`. Determinacy
rules out under-constrained outputs; it does not certify that an output is a
*canonical reduction*, which is a range property. The fix was not a stronger
analysis but a primitive (`bits`) that makes the range expressible, after which
the ordinary analysis proves the ordinary thing. See `docs/in-circuit-index.md`.

**Goldilocks wraps below 2⁶⁴, and rare is not sound.** `p = 2⁶⁴ - 2³² + 1`, so a
64-bit string is *not* a unique representative: whenever the canonical value is
below `2³² - 1`, the string for `c + p` is also 64 bits wide, also satisfies the
reconstruction, and has different low bits. A prover could shift the query index
for roughly one challenge in `2³²`. One constraint refuses every non-canonical
string and no canonical one. The test proves it is load-bearing rather than
defensive: on the sharpest case every other obligation is met and that assertion
alone refuses the witness.

**A spot check is not a proof.** The STARK originally checked its constraint
identity pointwise, at the positions the FRI queries happened to open — so the
committed trace was never asked to be a polynomial anywhere a query did not land,
and the positions follow publicly from the commitment. DEEP replaces that: the
identity is checked once at an out-of-domain point, and every committed column
enters one batched low-degree test. The test that gives it meaning builds a
prover whose column is corrupted at a single position no query opens, with an
honest low-degree quotient and impeccable Merkle openings — and watches it be
refused anyway. Cost: seven field elements.

---

## What is in the box

**Frontend (Haskell)** — lexer, parser, elaborator, the determinacy analysis and
its SMT escalation, an optimizer, and IR emission. Plus a language server
publishing determinacy diagnostics with the proof in the hover, a profiler
attributing constraint cost to source lines, and a gadget standard library.

**Backend (Rust)** — a neutral Core IR with an executable specification, a
witness solver, two independent lowerings, a hand-written Goldilocks field, FFT,
Merkle commitments, Poseidon, FRI, and the STARK.

Two invariants have held since the early phases, and both are demonstrated
rather than asserted:

1. **The Core IR is arithmetization-agnostic.** Proved by lowering the *same* IR
   two independent ways — R1CS and Plonkish — with identical results, and by
   measuring both: they tie on multiplication-shaped circuits and R1CS wins on a
   wide linear sum. Neither dominates, which is what justifies a neutral IR.
2. **Everything is generic over the field.** Proved by running the lowerings over
   a hand-written Goldilocks with identical constraint counts to BN254. Phase 5
   slid a new field and a whole prover *underneath* the compiler without changing
   a line of it.

A third thread runs through every phase: the **phase-0 forgery** — `IsZero` with
`inv` overridden to 0, `x = 5`, `out = 1`, satisfying one assertion while
claiming a false output. Every layer added since is tested to reject it.

---

## Pipeline

```
  .zkc source
      │  parse, elaborate
      ▼
  Core IR ──────────── determinacy proof (decidable core, then SMT)
      │                 executable spec + per-rule faithfulness + mutation harness
      │
      ├──► R1CS ─────┐
      └──► Plonkish ─┴──► AIR ──► FRI/STARK over Goldilocks ──► proof
                                        │
                                        └──► verified inside another circuit
```

The last arrow is real: `examples/fri_verify_idx.zkc` is a FRI verifier written
in the language itself, held to the same determinacy proof as any other circuit,
whose fold challenge *and* query position are derived in-circuit from the
transcript rather than taken on trust.

---

## Build and run

**Frontend.** Depends only on GHC boot libraries — no package manager in the
loop, so any modern GHC works.

```sh
make -C compiler all                       # → compiler/build/zkc
cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
    -o build/spec tests/Spec.hs && ./build/spec
```

**Backend.** Toolchain pinned in `rust-toolchain.toml`.

```sh
cd backend && cargo test
cargo build --bin zkc-stats                # arithmetization cost accounting
cargo build --bin zkc-profile              # per-source-line cost attribution
cargo build --bin zkc-check                # lower + self-check, --arith r1cs|plonkish
```

**Everything at once.** `scripts/run_all.sh` walks the pipeline end to end and
checks the generated artefacts are in sync first.

**Optional.** An SMT solver (`cvc5`, or `z3` with `--smt-dialect int`) for the
circuits outside the decidable fragment. Most of the stdlib does not need one.

---

## Layout

```
compiler/           Haskell frontend; boot libraries only
  src/Zkc/          syntax, determinacy analysis, SMT, IR, LSP, profiler
  tests/Spec.hs     172 frontend checks
std/                gadget stdlib — every gadget proved determinate,
                    every gadget with a negative fixture
  REFERENCE.md      generated by `zkc doc` from determinacy summaries
examples/           iszero, divide, relation, the FRI verifiers, the
                    determinate-but-unsound index binding and its fix
backend/
  zkc-core/         crypto-free, generic over ZkField: IR + executable spec,
                    witness solver, R1CS, Plonkish, field, FFT, Merkle,
                    Poseidon, FRI, STARK
  zkc-tools/        CLI tooling over the neutral IR; no proving system
scripts/            run_all.sh, and the generators for committed artefacts
docs/               roadmap, design decisions, per-phase reports, benchmarks,
                    CHECKPOINT.md (start here), and the two write-ups above
```

---

## Status

All seven roadmap phases are complete, and no core soundness boundary is open.

| Phase | Scope |
|---|---|
| 0–2 | Frontend, determinacy type system, R1CS, borrowed Groth16 prover |
| 3 | Gadgets, SMT escalation, constraint fusion |
| 4 | Own arithmetization: Plonkish from the same IR |
| 5 | Own prover: FRI/STARK over Goldilocks, retiring arkworks |
| 6 | Tooling: language server, profiler, gadget stdlib |
| 7 | Recursion + formal verification of the lowering |

**135 backend tests, 172/172 frontend checks, zero warnings.** Generated
artefacts — IR test fixtures, the `canonical_low` gadget family, the gadget
reference — are committed so the build stands alone, and each has a `--check`
proving it is still what its generator produces.

### Scope, drawn on purpose

- **Verification means equisatisfiability of the lowering, not a proof-assistant
  development.** The rigour here is executable specifications, SMT, differential
  and mutation testing — not Coq or Lean. What is verified is that *this*
  lowering implements *this* IR semantics.
- **The determinacy analysis is sound, not complete.** It proves determinacy or
  it does not; when it cannot settle a question it says so and escalates. A
  refusal to prove is never silently an approval.
- **Not audited, not production.** This is a from-scratch implementation built to
  be understood and argued with. The cryptographic soundness of FRI is the
  literature's; the engineering here is the compiler around it.

---

## Where to read next

- `docs/CHECKPOINT.md` — the resume-from-here snapshot: state, decisions and why,
  what is deliberately unfinished.
- `docs/DESIGN_DECISIONS.md` — the arguments, including the ones that were lost.
- `docs/in-circuit-index.md` — the determinate-but-unsound finding, and how it
  was closed. The best single read if you want to know what this project is for.
- `docs/phase5-status.md` — the own prover, and the boundary it shipped with,
  kept in the order it happened.
- `docs/benchmarks.md` — arithmetization costs, and the STARK against Groth16.

## License

See `LICENSE`.
