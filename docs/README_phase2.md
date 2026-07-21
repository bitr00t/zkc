# zkc — a zero-knowledge circuit compiler

**Phase 2: the type system.** A compiler that refuses to compile
under-constrained circuits, and tells you why.

Written from scratch: own language, own IR, own analyses. Haskell frontend,
Rust backend. No circuit-compiler framework is being wrapped — the only
borrowed component is the Groth16 prover itself (arkworks), which phase 5
replaces with an own FRI-based prover.

## The problem this phase solves

The dominant class of vulnerability in production ZK circuits is not a broken
proof system. It is an **under-constrained circuit**: the prover is given a
degree of freedom the author did not notice, and can produce a cryptographically
valid proof of a false statement. The proof system is doing its job perfectly —
it is faithfully proving a claim that does not mean what the author thought.

Phase 0 of this project demonstrated the attack end to end: a valid Groth16
proof that `5 == 0`. Phase 1 built a working compiler that would happily
produce exactly that circuit.

Phase 2 makes it a compile error.

```
$ zkc build examples/iszero_broken.zkc
error: output 'out' is not determined by the circuit's inputs
  --> examples/iszero_broken.zkc:14
      |
   14 |     output out: field;
      |
     = under the assumption x != 0, the constraints admit more than one value of 'out'
     = the prover also chooses the advice value 'inv' freely
     = so two witnesses can agree on every input and still disagree on 'out' —
       the prover picks which one to prove
help: add a constraint that forces 'out' in this case, then recompile
```

The compiler did not pattern-match a known bug. It *proved* that the correct
`IsZero` gadget is sound, tried to prove the same about this one, and reports
the branch where the proof fails.

## Quick start

```bash
make -C compiler all && make -C compiler test     # 54 checks
cd backend && cargo test && cargo build --release # 19 tests
./scripts/run_all.sh                              # the whole story
```

Requires GHC (≥ 9.4) and Rust (≥ 1.75). The compiler uses only GHC boot
libraries — no Hackage packages, no Stack, no Cabal.

## The language

```
circuit IsZero {
    private x: field;
    output out: field;

    gadget is_zero {
        advice inv = inv_or_zero(x);

        assert x * inv == 1 - out;
        assert x * out == 0;
    }
}
```

Three ideas carry the phase.

### 1. `output` is not `public`

Phase 1 had `private` and `public`, and that turned out to make the central
question ill-posed. "Is this value determined?" only has an answer once you
know whether the circuit is meant to *compute* it.

```
circuit Relation {
    public a: field;
    public b: field;
    assert a * b == 12;
}
```

This is a perfectly sound "I know a factorisation of 12" statement. Neither
`a` nor `b` is determined, and neither should be — `(2,6)` and `(3,4)` are
both legitimate witnesses. A checker demanding determinacy here would be
wrong.

So the language separates the roles: `private` and `public` are **inputs**
(the prover supplies them; nothing is claimed about where they came from),
while `output` is a value the circuit **computes** — and carries a proof
obligation. `Relation` compiles with "nothing to prove"; `IsZero` compiles
with a two-case proof.

### 2. `advice` is quarantined

`let` computes *and* constrains, so ordinary circuit code cannot create an
unconstrained value at all. `advice` computes *without* constraining — it is
the one construct that can silently make a circuit unsound.

It is therefore only legal inside a `gadget` block. Writing it becomes a
deliberate, greppable act rather than something that slips in during a
refactor. The block is the author saying: *I know this is subtle, and I claim
the assertions here pin the outputs down anyway.*

The determinacy pass then checks that claim.

### 3. Determinacy is proved, not assumed

Each assertion becomes a polynomial equation `P = 0` over the circuit's atoms
(declared wires and advice wires). Two rules are applied to exhaustion:

- **Linear propagation.** If an equation reads `c * u + r = 0` where `u` is
  the only undetermined atom and `c`, `r` are computable from determined
  atoms, and `c` is known nonzero, then `u = -r/c` is determined. Fields have
  no zero divisors, so a product of nonzero values is nonzero — that is what
  makes `c` checkable.
- **Case splitting.** When propagation stalls, branch on `w = 0` versus
  `w != 0` for some determined atom `w`. In the zero branch every monomial
  containing `w` vanishes; in the nonzero branch `w` unblocks coefficients.
  If *both* branches determine the outputs, so does the circuit.

Neither rule alone can verify `IsZero`. The proof needs the split:

```
$ zkc build examples/iszero.zkc --explain
  determinacy: 1 output(s) proved determined (out), 2 case(s)
    case x == 0      # x*inv == 1-out collapses to 0 == 1-out, so out = 1
    case x != 0      # x*out == 0 with x invertible, so out = 0
```

A branch whose equations reduce to a nonzero constant is *infeasible* — no
witness exists there — and counts as discharged. That is how `Divide` works:

```
$ zkc build examples/divide.zkc --explain
  determinacy: 1 output(s) proved determined (q), 2 case(s)
    case b == 0      # b * inv_b == 1 becomes 0 == 1: no witness exists
    case b != 0      # inv_b determined, then q determined through it
```

Note what is **not** required: advice wires need not be determined. When
`x = 0`, `IsZero`'s helper `inv` genuinely may be anything, and the circuit is
still sound because `out` is pinned regardless. A checker that demanded every
advice wire be determined would reject correct code. Soundness is about
outputs.

## Soundness travels with the artifact

The emitted IR (schema v2) carries the proof:

```json
"determinacy": {
  "proved": true,
  "targets": ["out"],
  "branches": [["x == 0"], ["x != 0"]]
}
```

The Rust backend **refuses to prove** an IR that declares outputs without a
discharged proof, and a missing record deserializes to `proved: false` rather
than defaulting to allow. Soundness is a claim about *this circuit*, not about
the toolchain that happened to produce it — so it is checked at the point of
use, not asserted in a README.

## What it does not do

The analysis is **incomplete, and deliberately conservative**: a failure means
"not proved", not "proved unsound". Since the pass rejects on failure,
incompleteness costs expressiveness — never safety.

Concretely:

- Case splitting is depth-bounded (3). Deeper proofs are refused, not guessed.
- Polynomial expansion is exponential in the worst case, with a hard cap and a
  clear error rather than a hang.
- Degree ≥ 2 in the unknown is never solved: `z * z == 4` has two roots, so
  `z` is correctly reported as undetermined.
- Gadgets are quarantine markers, not scopes or reusable definitions yet.

Phase 3 addresses the first two by escalating to an SMT solver when the
decidable fragment gives up, and the last by making gadgets parameterised
definitions.

## Layout

```
compiler/                 Haskell frontend (GHC boot libraries only)
  src/Zkc/Syntax/         lexer, parser, AST
  src/Zkc/Core/           elaboration, Core IR, optimizer
  src/Zkc/Analysis/       Poly.hs (multivariate polys over F_p)
                          Determinacy.hs (the proof search)
  src/Zkc/Diagnostics.hs  source-quoting error messages
  src/Zkc/Field.hs        field moduli
  test/Spec.hs            54 checks, hand-rolled harness
backend/                  Rust
  zkc-core/               IR loading + validation, witness solver,
                          R1CS lowering and checker
  zkc-prove/              arkworks Groth16 bridge + CLI
examples/                 .zkc circuits, including two that must NOT compile
ir-spec/SCHEMA.md         the Haskell/Rust contract, versioned
docs/                     design decisions and roadmap
```

## Notes on the environment

- The compiler depends on **nothing** outside GHC's boot libraries — lexer,
  parser and JSON writer are hand-rolled. `make all` is the whole build.
- `rust-toolchain.toml` pins 1.75.0 and `Cargo.lock` pins four transitive
  dependencies to their last 1.75-compatible releases (`zeroize`,
  `zeroize_derive`, `rayon`, `rayon-core`). On a modern toolchain both pins
  can simply be deleted.
