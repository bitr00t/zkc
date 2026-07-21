# zkc — phase 3: gadgets become definitions

A zero-knowledge circuit compiler built from scratch: **Haskell frontend,
Rust backend**. Phase 2 made under-constraining a *compile error* — the
determinacy pass proves each declared output is a function of the inputs, or
refuses to emit. Phase 3 makes that guarantee **compose**: gadgets stop being
inline markers and become parameterised, reusable definitions, and the proof
follows them — a gadget is proved once, and every call site reuses the result
instead of re-deriving it.

```
.zkc source ──▶ lexer ──▶ parser ──▶ elaborate ──▶ Core IR ──▶ passes ──▶ JSON
                          (program)      │  │       ( Haskell )             │
                                         │  └─▶ Body skeletons ─┐           ▼
                                         │                      │   (Rust backend,
                                  determinacy ◀─ summaries ◀────┘    unchanged)
                                  (compositional)
```

The pipeline is the phase-2 pipeline with two changes: elaboration now parses
a **program** (gadget definitions plus one circuit) and produces, alongside
the flat IR, a *skeleton* per scope; and the determinacy pass consumes those
skeletons compositionally rather than expanding the whole inlined circuit.

```bash
make -C compiler test      # 74 checks, hand-rolled harness, GHC boot libs only
make -C compiler all       # build the `zkc` CLI
./compiler/build/zkc build examples/divide.zkc --explain
```

Requires GHC (tested on 9.4.7). The compiler still uses **only GHC's boot
libraries** — no cabal, no Hackage, `make` and go.

## Phase 3 is three workstreams

Phase 3 has three independent pieces. The design note (`docs/phase3.md`)
argues for the order **A → C → B**: A is a prerequisite for both of the
others (compositional determinacy keeps B's SMT queries small, and reusable
gadgets are what let you *write* the SHA-256 / Merkle circuits C benchmarks).

| | Workstream | Status |
|---|---|---|
| **A** | Gadgets as parameterised definitions + compositional determinacy | **done** |
| C | Constraint-count optimization (assertion fusion), benchmarked vs Circom | next |
| B | SMT escalation: three-valued proved / refuted / unknown | after C |

This README documents **Workstream A**, which is implemented and tested. B and
C are specified at the end.

## What Workstream A delivers

**Gadgets are top-level definitions.** A source file is now a *program*: zero
or more gadget definitions plus exactly one circuit. A gadget has field-typed
parameters, field-typed results, and optional `require` preconditions.

```rust
gadget is_zero(x: field) -> (out: field) {
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

**Real scopes.** A gadget body is its own scope: its bindings do not leak into
the circuit, and the circuit's bindings are not visible inside it — only
parameters and results cross the boundary. Each instantiation gets **fresh
wires**, so calling the same gadget twice can never accidentally share state.
These were exactly the properties phase-2 marker gadgets lacked.

**Two call forms, one per result kind.** A result the body only *constrains*
(a bare atom, like `out` above) binds to an already-declared output:

```rust
(out) = is_zero(x);
```

A result the body *computes* — produced by `advice` or `let` — is bound
freshly with `let`:

```rust
let (inv_b) = reciprocal(b);
assert q == a * inv_b;
```

Instantiation is always a *statement*, never a sub-expression, so elaboration
never inlines inside an expression tree, and the `(` after `let`
disambiguates a fresh-result instance from a scalar `let`.

**Compositional determinacy.** Each gadget is proved **once**, as its own
little determinacy problem — its parameters determined, its results the
targets — yielding a `Summary`. At a call site the summary is *applied*: the
results are marked determined and any nonzero guarantee is recorded, without
re-expanding the body into the caller's polynomial system. Gadgets are proved
in dependency order (callees first); cycles are rejected, because a circuit is
finite and gadgets cannot recurse.

**Preconditions.** `require p != 0` is both an assumption the gadget's proof
may lean on and an obligation each call site must discharge from its own
nonzero context. A gadget also *exports* the parameters its body forces
nonzero (detected by the same infeasibility argument the proof already uses),
so one gadget's guarantee can discharge another's requirement.

## The example rewrite, and the point of it

`examples/iszero.zkc` and `examples/divide.zkc` are rewritten from phase-2
inline gadgets to phase-3 definitions. The claim being tested is that the
rewrite is **behaviour-preserving**: the flat IR handed to the backend is the
same.

It is — byte for byte, modulo the `"line"` fields that legitimately move when
the definition relocates to the top of the file. Same wires, same operations,
same assertions, same determinacy record (`branches: [["x == 0"],["x != 0"]]`
for `IsZero`, `[["b == 0"],["b != 0"]]` for `Divide`). The two examples also
exercise both call forms: `is_zero`'s `out` is an atom result (`(out) = ...`),
`reciprocal`'s `inv_b` is a computed result (`let (inv_b) = ...`).

**Why this matters more than it looks.** Composition is not just ergonomics —
it changes what is *provable*. Four independent `is_zero` instances each need
their own `x == 0` / `x != 0` case split; four splits exceed the depth bound,
so proving them all at once on the inlined IR **gives up**. Proving the gadget
once and reusing the summary four times **succeeds**. Same circuit, one path
fails and the other holds:

```
Many (four is_zero instances)
  monolithic (inlined IR)   →  rejected: 4 case splits exceed depth bound 3
  compositional (summaries) →  proved: one gadget proof, reused four times
```

That is the property the phase-3 design note calls the prerequisite for
everything downstream: without it, a 32-deep Merkle path is unprovable by the
decidable fragment, and there is nothing small enough to hand an SMT solver.
The per-gadget case analyses also **concatenate** in the report (2N paths for
N instances), rather than exploding into a 2^N cross-product.

## Design decisions worth naming

Full reasoning is in `docs/phase3.md`; the load-bearing choices:

**Results are output-parameters.** The IR already represents a
"constrained-not-computed" wire exactly one way — as a declared output pinned
by assertions. Making gadget results the same shape means the backend, the IR
schema, and the JSON emitter learn nothing new, and the rewritten examples
produce identical IR. Results the body computes (via `advice`/`let`) are also
usable, which required a small, backward-compatible extension to the
determinacy pass so a *node* (not just an atom) can be a target.

**Determinacy runs before optimization now.** Phase 2 ran it after, to keep
polynomial expansion cheap. Compositional proofs are already small
per-gadget, so that rationale is gone; running before optimization lets the
proof see the gadget structure directly. Optimization preserves the solution
set, so a proof valid before it stays valid after.

**A gadget's internal splits stay internal.** They are discharged inside its
summary; the caller sees "results determined" plus any nonzero guarantee, not
the callee's case analysis. This is what keeps the query the caller reasons
about small — the whole point of composition.

## Scope, drawn on purpose

- **Intermediate composition is deferred.** Results bind to declared outputs
  or to body-computed wires. Feeding a gadget's result as a *fresh,
  non-output* intermediate into a further expression — Poseidon-in-Merkle
  style — needs a wire that is pinned only by constraints and has no defining
  node, which touches the Rust witness solver and the IR schema. That is
  follow-up work; deep reuse here is demonstrated with many output-binding
  instances.
- **`require` is a precondition, not an enforcement.** The caller must
  establish the nonzero fact (from a nonzero literal or a prior gadget's
  guarantee); the gadget does not add a constraint to make it true. Neither
  shipped example needs it — `Divide` works through the internal
  infeasibility of `b == 0` — so the syntax is there for the standard library
  to come.
- **The backend was not re-run in this iteration.** Backend compatibility is
  established by the IR byte-diff against the phase-2 output, not by an
  end-to-end proof, because this change is frontend-only by construction.

## Layout (what changed)

```
zkc/
├── compiler/src/Zkc/
│   ├── Syntax/Lexer.hs     #  + `require`, `!=`
│   ├── Syntax/Ast.hs       #  + GadgetDef, Program, Require, SInstance
│   ├── Syntax/Parser.hs    #  program grammar: definitions + one circuit
│   ├── Core/Ir.hs          #  + InstanceSite, Body (the determinacy skeleton)
│   ├── Core/Elaborate.hs   #  scopes, inlining, and skeletons in one pass
│   ├── Analysis/Determinacy.hs  #  checkProgram, summaries, searchWith
│   └── Main.hs             #  program pipeline; determinacy before optimize
├── examples/
│   ├── iszero.zkc          #  rewritten: atom-result call form
│   └── divide.zkc          #  rewritten: computed-result call form
└── compiler/tests/Spec.hs  #  74 checks
```

The backend (`backend/`), the IR schema (`ir-spec/SCHEMA.md`), and the JSON
emitter are untouched.

## Tests

`make -C compiler test` — 74 checks (up from 54). Beyond the phase-2 suite,
re-pointed at the new syntax:

- **parser** — gadget signatures, both instance forms, `require` at the body
  head, "exactly one circuit".
- **scoping** — internal bindings do not leak; each instance gets fresh wires.
- **elaboration** — unknown gadget, arity mismatch, dead advice inside a
  gadget.
- **compositional** — `IsZero`/`Divide` proved by summary with branches
  remapped to the caller; four instances proved by reuse; the *same* circuit
  rejected monolithically (the scaling test); branches concatenate, not
  explode.
- **require** — a gadget provable only under its precondition; the
  precondition discharged by a prior guarantee; an undischarged precondition
  as a compile-time failure.
- **golden** — the rewritten examples inline to the phase-2 shape.

## Next

**Workstream C — constraint-count optimization.** Phase 2's optimizer does
constant folding, CSE and DCE. Competitive lowering needs
multiplicative-assertion fusion: `assert a*b == c` currently lowers to two
R1CS constraints where R1CS expresses it in one. The fusion belongs in the
backend's `lower.rs`, not in `Passes.hs`, to keep the Core IR
arithmetization-neutral. Benchmarked against Circom on SHA-256 and Merkle
inclusion — circuits that Workstream A's reusable gadgets now make writable.

**Workstream B — SMT escalation.** When the decidable fragment gives up, emit
the residual question to an SMT solver over the field instead of rejecting.
The decidable core stays the fast path; the solver handles the tail, and —
crucially — distinguishes **refuted** (with a counterexample: two witnesses
agreeing on inputs, disagreeing on an output) from **unknown**, where phase 2
collapses both into "rejected". A refutation hands the author the exact
attack. Composition from Workstream A is what keeps each query small enough to
be answerable.

See `docs/ROADMAP.md` for phases 4–7.
