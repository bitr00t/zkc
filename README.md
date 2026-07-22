# zkc — phase 3: gadgets, cheaper constraints, and honest answers

A zero-knowledge circuit compiler built from scratch: **Haskell frontend,
Rust backend**. Phase 2 made under-constraining a *compile error* — the
determinacy pass proves each declared output is a function of the inputs, or
refuses to emit. Phase 3 does three things to that guarantee: makes it
**compose**, makes the resulting circuits **cheap**, and makes the compiler's
answer **honest** when it cannot decide.

```
.zkc source ──▶ lexer ──▶ parser ──▶ elaborate ──▶ Core IR ──▶ passes ──▶ JSON
                          (program)      │  │       ( Haskell )             │
                                         │  └─▶ Body skeletons ─┐           ▼
                                         │                      │      lower.rs
                                  determinacy ◀─ summaries ◀────┘     (+ fusion)
                                  (compositional)                         │
                                         │ stalls?                        ▼
                                         └──▶ SMT ──▶ proved / refuted / unknown
```

```bash
make -C compiler test      # 90 checks, hand-rolled harness, GHC boot libs only
make -C compiler all       # build the `zkc` CLI
cargo test --manifest-path backend/Cargo.toml -p zkc-core   # 24 checks

./compiler/build/zkc build examples/divide.zkc --explain
./compiler/build/zkc build examples/iszero_broken.zkc --smt-solver z3 --smt-dialect int
```

Requires GHC (tested on 9.4.7) and, for escalation, an SMT solver. The
compiler still uses **only GHC's boot libraries** — `process` is one of them,
so shelling out to a solver costs no dependency.

## The three workstreams

| | Workstream | Status |
|---|---|---|
| **A** | Gadgets as parameterised definitions + compositional determinacy | **done** |
| **C** | Constraint-count optimization (multiplicative-assertion fusion) | **done**; Circom benchmark blocked on the stdlib |
| **B** | SMT escalation: proved / refuted / unknown | **done**; the `QF_FF` path is unverified against a solver |

The order was **A → C → B**, as the design note argues: A is a prerequisite
for both. Compositional determinacy keeps B's queries small, and reusable
gadgets are what let you *write* the circuits C benchmarks.

---

## Workstream A — gadgets become definitions

A source file is now a *program*: gadget definitions plus one circuit.

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

**Real scopes.** A gadget body is its own scope; only parameters and results
cross the boundary. Each instantiation gets **fresh wires**, so calling the
same gadget twice cannot accidentally share state.

**Two call forms.** A result the body only *constrains* (a bare atom, like
`out`) binds to a declared output: `(out) = is_zero(x);`. A result the body
*computes* — via `advice` or `let` — is bound freshly:
`let (inv_b) = reciprocal(b);`. Instantiation is always a statement, never a
sub-expression.

**Compositional determinacy.** Each gadget is proved **once** — parameters
determined, results the targets — yielding a `Summary`. At a call site the
summary is *applied*, never re-expanded. Gadgets are proved callees-first;
cycles are rejected, because a circuit is finite.

**Preconditions.** `require p != 0` is both an assumption the gadget's proof
may lean on and an obligation each call site discharges. A gadget also
*exports* the parameters its body forces nonzero, so one gadget's guarantee
can discharge another's requirement.

### Why composition changes what is provable

Four independent `is_zero` instances each need their own `x == 0` / `x != 0`
split; four splits exceed the depth bound, so proving them on the inlined IR
**gives up**. Proving the gadget once and reusing the summary **succeeds**:

```
Many (four is_zero instances)
  monolithic (inlined IR)   ->  rejected: 4 case splits exceed depth bound 3
  compositional (summaries) ->  proved: one gadget proof, reused four times
```

Per-gadget case analyses also **concatenate** in the report (2N paths for N
instances) rather than exploding into a 2^N cross-product.

The rewritten `examples/iszero.zkc` and `examples/divide.zkc` produce IR that
is **byte-identical** to phase 2's, modulo the `line` fields that legitimately
move when a definition relocates — so the rewrite is behaviour-preserving.

---

## Workstream C — constraint-count optimization

Prover cost is **R1CS constraint count**, not IR node count. The most common
shape in a real circuit is `assert a * b == c`, and lowered naively it costs
**two** rank-1 constraints — `a * b = v`, then `(v - c) * 1 = 0` — for
something R1CS expresses natively in **one**: `a * b = c`.

When a `mul` wire feeds exactly one assertion and nothing else, its
intermediate variable is pure overhead. `lower.rs` now skips it and emits the
fused constraint directly.

The analysis is precise: in `(a*b)*(a*b)` the inner product feeds the outer
multiplication, so it keeps its variable; only the outer one folds. And when
both sides of an assertion are fusible, only one folds — a rank-1 constraint
has a single product.

This lives in the **lowering**, not in `Passes.hs`: that `a * b == c`
collapses to one rank-1 constraint is an R1CS fact, and a future AIR backend
packs differently from the same IR. Keeping it out of the neutral passes
preserves the arithmetization-neutrality invariant.

**Measured** (both pinned as tests, and `lower_with(ir, false)` reproduces the
phase-2 lowering exactly so the win is a delta, never an assertion):

```
BENCH circuit=ManyProducts n=64 constraints_unfused=128 constraints_fused=64 \
      vars_unfused=257 vars_fused=193 reduction=0.50
```

End to end through the real compiler, `benchmarks/many_mul.zkc` — eight
instances of one reused gadget — lowers to **8 constraints instead of 16**.
Correctness travels with cost: a test checks that both lowerings accept the
honest witness and reject a forged output, so the count never shrinks by
breaking soundness. See `docs/benchmarks.md`.

---

## Workstream B — SMT escalation

Phase 2's answer to "I could not prove this" was to reject, collapsing two
very different situations: *this circuit is genuinely under-constrained* and
*my incomplete analysis could not decide*. The first is a bug in the user's
code; the second is a limitation of ours. Phase 3 tells them apart.

```haskell
data DeterminacyResult
  = Proved   Report          -- emit
  | Refuted  Counterexample  -- print the forgery, refuse
  | Unknown  Residual        -- say so honestly, refuse
```

### The query: uniqueness as self-composition

Determinacy is a two-copy property. Take two witnesses, assert both satisfy
every constraint, assert they agree on every input, and ask whether they can
still **disagree on an output**. `unsat` proves; `sat` *is* the forgery;
anything else is unknown.

### The headline

```
$ zkc build examples/iszero_broken.zkc --smt-solver z3 --smt-dialect int

error: 'is_zero' is under-constrained — the solver constructed a forgery
  --> examples/iszero_broken.zkc:20
   20 | gadget is_zero(x: field) -> (out: field) {
     = two witnesses satisfy every constraint and agree on all inputs:
     =     x = 1
     = but disagree on:
     =     out = 0   vs   out = 1
     =   witness 1 chooses: inv = 1
     =   witness 2 chooses: inv = 0
     = the prover picks whichever it prefers, and proves it
```

Check it by hand: `x*inv = 1 = 1-out` gives `out = 0`; `x*inv = 0 = 1-out`
gives `out = 1`. Both satisfy the one remaining assertion. That is the attack,
not a description of one.

### Two dialects behind one interface

Field arithmetic has a purpose-built theory, `QF_FF`, which reasons over the
field directly. It is the right target and the default. It is also not
universally available — it needs a solver built with finite-field support,
which stock builds routinely omit. So the query is emitted through a
`Dialect`, and a second dialect encodes the same question as integers in
`[0,p)` with explicit `mod`, accepted by any `QF_NIA` solver.

The integer encoding is weaker in a predictable way: nonlinear integer
arithmetic is undecidable, so solvers find counterexamples readily and time
out trying to prove their absence. Which is exactly what `Unknown` is for.

### One asymmetry that is load-bearing

When a scope instantiates gadgets, their results appear as free atoms while
the constraints pinning them down stay in the callee — that is what makes
composition cheap. The system handed to the solver is therefore a
**relaxation**: it admits at least every witness the real circuit does. So

* `unsat` on a relaxation implies `unsat` on the real circuit — a **proof
  carries over**;
* `sat` may be an artifact of the omitted constraints — a **refutation does
  not**, and is downgraded to `Unknown`.

Getting this backwards would let the compiler accuse correct code of being
forgeable, which is worse than saying nothing.

### Layering

Escalation never replaces the decidable core; it follows it, and only for the
one scope that stalled — which is what Workstream A bought. When a solver
discharges a *gadget*, the result is fed back as an assumed summary and the
compositional proof resumes, so one escalation unblocks every call site. The
assumed summary is deliberately weak (no case splits, no exported nonzero
facts), so assuming it can never make a caller succeed for a reason the solver
did not establish.

```
--no-smt        skip escalation (exact phase-2 behaviour)
--smt-solver    solver executable (default: cvc5)
--smt-dialect   ff = QF_FF (default) | int = QF_NIA
--smt-timeout   seconds
--dump-smt      write the query out for inspection
```

---

## Scope, drawn on purpose

- **Intermediate composition is deferred.** Results bind to declared outputs or
  to body-computed wires. Feeding a gadget's result as a *fresh, non-output*
  intermediate into further computation — Poseidon-in-Merkle style — needs a
  wire pinned only by constraints and with no defining node, which touches the
  Rust witness solver and the IR schema. That is the next follow-up, and it is
  what unblocks the standard library.
- **The Circom benchmark has not been run.** SHA-256 and Merkle inclusion need
  the stdlib from the point above. The methodology is written down in
  `docs/benchmarks.md`; `benchmarks/many_mul.zkc` stands in, exercising the
  same fusion on the same constraint shape.
- **The `QF_FF` path is syntactically verified but unsolved.** cvc5 accepts
  the generated query — the logic, sort and assertions all parse — but stock
  builds lack the finite-field configuration, so no solver in this environment
  actually answered one. The `Proved` (unsat) path is implemented and tested,
  but has never been triggered by a real solver here. Both should be re-checked
  against a finite-field-capable build.
- **`require` is a precondition, not an enforcement.** The caller must
  establish the nonzero fact; the gadget does not add a constraint to make it
  true.

## Layout

```
zkc/
├── compiler/src/Zkc/
│   ├── Syntax/{Lexer,Ast,Parser}.hs   # A: program grammar, require, instances
│   ├── Core/{Ir,Elaborate}.hs         # A: scopes, inlining, Body skeletons
│   ├── Analysis/Determinacy.hs        # A: summaries;  B: ProgramFailure, BodySystem
│   ├── Analysis/Smt.hs                # B: query, dialects, solver, counterexample
│   ├── Analysis/Poly.hs               # B: `terms`, so polynomials can be re-emitted
│   └── Main.hs                        # B: three-valued verdict, escalation loop
├── backend/zkc-core/src/lower.rs      # C: multiplicative-assertion fusion
├── examples/                          # rewritten to phase-3 syntax
├── benchmarks/many_mul.zkc            # C: the fusion benchmark, end to end
└── docs/benchmarks.md                 # C: methodology and results
```

The IR schema (`ir-spec/SCHEMA.md`) and the JSON emitter are untouched:
gadgets inline away, and the escalation's verdict is a compile-time artifact.

## Tests

`make -C compiler test` — **90 checks** (from 54). Beyond phase 2's suite:
gadget signatures and both call forms; scoping and wire freshness; unknown
gadget and arity errors; compositional proofs with remapped branches; the
four-instance scaling test (proved compositionally, *rejected* monolithically);
`require` discharge and failure; SMT query construction in both dialects;
preconditions assumed in both copies; the relaxation flag; and solver-answer
parsing including timeouts, errors, and field literals.

`cargo test -p zkc-core` — **24 checks** (from 19): fusion counts fused and
unfused, fusion precision, satisfaction preservation, and both benchmarks.

## Next

1. **Intermediate composition** — fresh non-output result wires, in the IR
   schema and the Rust witness solver. Unblocks the standard library.
2. **The stdlib and the real benchmark** — Poseidon, SHA-256, Merkle; then the
   Circom comparison `docs/benchmarks.md` specifies.
3. **A finite-field solver** — verify the `QF_FF` path and exercise `Proved`.

See `docs/ROADMAP.md` for phases 4–7.
