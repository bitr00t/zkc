# zkc — phase 1: the walking skeleton

A zero-knowledge circuit compiler built from scratch: **Haskell frontend,
Rust backend**. Phase 1 is the walking skeleton — a thin but *complete* path
from a source file to a verified proof, so that every later phase has
somewhere to land.

```
.zkc source ──▶ lexer ──▶ parser ──▶ elaborate ──▶ Core IR ──▶ passes ──▶ JSON
                                    ( Haskell )                              │
                                                                             ▼
        proof ◀── Groth16 ◀── R1CS ◀── lower ◀── validate ◀── Core IR ── (Rust)
                                 ▲
                          witness solver
```

```bash
./scripts/run_all.sh      # build both halves, run both test suites, walk the pipeline
```

Requires GHC (tested on 9.4.7) and Rust (tested on 1.75). The compiler uses
**only GHC's boot libraries** — no cabal, no Hackage, `make` and go.

## What phase 1 delivers

**A real language, however small.** Three statement forms, and the one that
matters is the distinction the whole project exists for:

```rust
circuit IsZero {
    private x: field;
    public out: field;

    advice inv = inv_or_zero(x);      // computed, NOT constrained

    assert x * inv == 1 - out;
    assert x * out == 0;
}
```

`let` computes *and* constrains. `advice` computes *without* constraining —
the "unsafe" of ZK. A prover is free to substitute any value it likes for an
advice wire; only assertions pin it down.

**An arithmetization-agnostic Core IR** (`ir-spec/SCHEMA.md`). A typed
constraint graph — field operations, hints, assertions — that says nothing
about R1CS. That neutrality is the point: phase 5's hand-written FRI prover
consumes AIR traces, which are structurally unlike R1CS equation systems, and
an IR shaped like either could not lower to the other.

**Real optimization passes**: constant folding, CSE, dead-code elimination,
with wire renumbering. `--no-opt` turns them off so you can diff the IR.

**A backend that checks its input.** The IR is validated on load (dense wires,
topological order, arity, schema version) rather than trusted. A frontend bug
that reordered nodes would otherwise miscompile silently — and here a
miscompiled circuit is a security hole.

**Source-level errors from the backend.** Assertions carry their original text
and line number through the IR, so a violated constraint reads:

```
constraint system NOT satisfied — refusing to prove:
  [3] line 18: (x * out) == 0
      left-hand side = 5, right-hand side = 0
```

## The demo, and the point of it

`scripts/run_all.sh` ends with two runs that differ by **one line of source**:

- `examples/iszero.zkc` — a forged claim ("5 is zero", with the advice wire
  overridden) is caught by the self-check and refused, naming the assertion.
- `examples/iszero_broken.zkc` — the same forged claim yields a
  **cryptographically valid Groth16 proof that 5 == 0**, and the verifier
  accepts it.

Nothing is wrong with the proof system. The constraint system simply never
asked the question. This is the bug class the project exists to eliminate,
now reproducible from source through the real compiler rather than a
hand-written spike.

## The known gap (and why it is on purpose)

Phase 1's determinacy check is a deliberate approximation: every advice wire
must be *mentioned* by some assertion. That catches the crudest error —
`examples/unconstrained_advice.zkc` is rejected — and nothing subtler.

`iszero_broken.zkc` passes every check phase 1 has and is still forgeable.
That gap is the specification for **phase 2**: `Determined` vs `Advice` as
real types, `hint` quarantined inside `gadget` blocks, and a determinacy pass
that must *prove* the assertions pin each advice wire down uniquely (a
decidable syntactic fragment first, SMT escalation later).

## Layout

```
zkc/
├── compiler/              # Haskell — GHC boot libraries only
│   ├── src/Zkc/Syntax/    #   Lexer, Parser, Ast
│   ├── src/Zkc/Core/      #   Ir, Elaborate (scope + kind checks), Passes
│   ├── src/Zkc/Emit/      #   Json (hand-rolled)
│   ├── src/Main.hs        #   `zkc build file.zkc -o out.json`
│   ├── test/Spec.hs       #   27 checks, hand-rolled harness
│   └── Makefile
├── ir-spec/SCHEMA.md      # the Haskell/Rust contract, versioned
├── backend/
│   ├── zkc-core/          # IR loading + validation, witness solver,
│   │                      #   R1CS lowering, satisfiability checker.
│   │                      #   Generic over the field, no cryptography.
│   └── zkc-prove/         # arkworks Groth16 over BN254 + the CLI
├── examples/*.zkc         # incl. one deliberately vulnerable, one rejected
├── inputs/*.json          # prover inputs, incl. the forgery
├── scripts/run_all.sh
└── docs/
```

## Tests

- `make -C compiler test` — 27 checks: lexing, parsing, error messages,
  scope/kind rules, each optimizer pass, JSON emission.
- `cargo test --manifest-path backend/Cargo.toml` — 17 checks: field parsing,
  every IR validation rule, lowering cost model, and the forgery behaviour on
  both circuits.

The backend tests use hand-written IR fixtures rather than compiler output, on
purpose: they pin the *contract*, so they fail if the backend's reading of the
schema drifts even when the frontend drifts with it. End-to-end agreement is
covered by `scripts/run_all.sh`.

## Notes

- `Cargo.lock` is committed and pins `zeroize` and `rayon-core` to releases
  that build on Rust 1.75. On a newer toolchain you can drop those pins.
- Groth16 setup uses a deterministic RNG so runs are reproducible. A real
  deployment needs a multi-party trusted setup — whoever knows that randomness
  can forge proofs for any statement.
- The compiler avoids Hackage entirely (boot libraries only). If you would
  rather use `megaparsec`/`aeson`, the module boundaries are already in the
  right places.

## Next

Phase 2 — the type system: `Determined`/`Advice` in the IR, `gadget`
quarantine, the determinacy pass, and first-class error messages. See
`docs/ROADMAP.md`.
