# Design decisions

The choices worth arguing about, and why they went the way they did.

## Haskell frontend, Rust backend

Compilers are algebraic-data-type-shaped: ASTs, IRs, pattern matching over
node kinds, passes as pure functions. Haskell makes that code short and makes
adding an IR node a type error everywhere it must be handled. Provers are the
opposite workload — tight loops over field elements, NTTs, Merkle trees, where
predictable performance and no GC pauses matter. Rust owns that.

The seam is the serialized Core IR. It is a real artifact with a versioned
schema, validated on both sides, so the two halves can be developed and
debugged independently.

## The Core IR is arithmetization-agnostic

The single most consequential decision, and the most expensive to retrofit.

The IR is a typed constraint graph: field operations, hints, assertions. It
does *not* encode R1CS. R1CS is an unordered system of rank-1 equations over
one global witness vector; AIR — what a FRI/STARK prover consumes — is an
execution-trace table with transition constraints between adjacent rows. They
are structurally different, and an IR shaped like either cannot be lowered to
the other.

The cost model lives in the backend, not the IR. In `lower.rs`, `add`, `sub`
and `neg` are free (they fold into linear combinations) while `mul` costs a
variable and a constraint. Under an AIR backend that same arithmetic would
cost trace columns. Had the IR baked in "linear operations are free", phase 5
would have meant a rewrite.

## Everything is generic over the field

R1CS + Groth16 wants a ~254-bit pairing-friendly field (BN254). FRI wants a
small, high-two-adicity field (Goldilocks, `2^64 - 2^32 + 1`), where a 254-bit
field would be a performance disaster. So the field is a parameter everywhere:
the IR names it (`"field": "bn254"`), and `zkc-core` is generic over a
`ZkField` trait with a blanket impl for arkworks' `PrimeField`. Phase 5's
hand-rolled field implements the same trait and the rest of the compiler keeps
working.

## Borrow the prover, for now

Phases 1–3 use arkworks' Groth16. Writing a prover is phase 5's whole job; the
point of a walking skeleton is a *complete* pipeline early, so that later work
has a place to attach. Confining the dependency to `zkc-prove` keeps it
swappable — `zkc-core` has no cryptography in it at all.

## `let` versus `advice`

The language has two binding forms because the bug class this project targets
lives exactly in the gap between them.

`let` computes *and* constrains, so ordinary circuit code is sound by
construction. `advice` computes *without* constraining: the value is whatever
the prover supplies. Most ZK vulnerabilities are an advice wire that some
assertion was supposed to pin down and didn't.

Making that difference **syntactic** means it can be type-checked. Circom's
`<--` and `<==` prove the ergonomics work; the plan from phase 2 is to go
further and require a *proof* of determinacy rather than trusting the author
to have written enough assertions.

## Hints are a closed set

`advice` may only be bound to a known hint (`inv_or_zero`, `inv`), not to an
arbitrary expression. Every hint is a proof obligation the determinacy pass
will have to discharge, so the set must be enumerable. It also produces better
errors today: `advice w = x * x;` is rejected with "that is not a hint" rather
than a parse error about a missing parenthesis.

## Advice names survive into the IR

`hint` nodes carry their source-level name. Two reasons: diagnostics should say
`inv`, not `wire 3`; and the prover CLI can *override* an advice wire by name.
That override is not a debugging convenience — advice is by definition
prover-chosen, so modelling a dishonest prover requires being able to say so
out loud. It is what makes the forgery demo real rather than narrated.

## The backend validates the IR instead of trusting it

Dense wire numbering, topological order, arity, schema version. A frontend bug
that emitted a forward reference would otherwise silently miscompile a
circuit, and here a miscompiled circuit is a security hole. The cost is a few
dozen lines; the alternative is a class of bug that surfaces as "the verifier
accepted something it shouldn't have".

## Self-check before proving

After lowering, the backend evaluates every constraint against the assignment
itself before calling Groth16. Two payoffs: a violated constraint is reported
against the user's source line and text, and the failure mode is a clean
refusal instead of an assertion firing deep inside the proving library.
(arkworks' prover asserts satisfiability internally and panics — a bad user
experience to inherit.)

## JSON, and constants as strings

JSON because for the first stretch of a compiler's life, reading the IR in a
diff and pasting it into a bug report is worth more than serialization speed.
Constants are decimal *strings* because field elements routinely exceed 64
bits and JSON numbers cannot carry them safely.

Optimizer-folded constants may be negative: folding happens over the integers
and the backend reduces modulo whichever prime it instantiates. That is what
keeps constant folding field-agnostic.

## Hints are never folded or shared

CSE merges structurally identical nodes — except hints. A hint is an effect
("ask the witness generator"), and two hint nodes represent two independent
free choices by the prover. Silently merging them would change which values a
prover may pick, i.e. change the security properties of the circuit. The
optimizer must never do that.

## No external Haskell packages

The compiler builds with GHC's boot libraries only: hand-rolled lexer, parser
and JSON writer. Partly circumstance (Hackage was unreachable in the build
environment), partly a real benefit — `make` and go, no package manager in the
loop, and the whole frontend is auditable. The module boundaries are
conventional, so swapping in `megaparsec` or `aeson` later is local surgery.

## The phase-1 determinacy check is knowingly too weak

Every advice wire must be *mentioned* by some assertion. It catches the
crudest error and nothing subtler: `examples/iszero_broken.zkc` passes it and
is still forgeable.

That is not an oversight left lying around — it is the specification for phase
2, kept as an executable example so the improvement can be measured rather
than asserted.
