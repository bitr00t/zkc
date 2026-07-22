# Design decisions — phase 2

Decisions worth writing down, with the reasoning that produced them.

## Splitting `public` into `public` and `output`

**The problem.** The phase-2 goal was "prove that values are determined". Two
days of that goal being obviously right hid the fact that it was not yet a
*question*: determined values are values the circuit computes, and phase 1's
type system could not say which those were.

`public a; public b; assert a * b == 12;` is a sound circuit. Nothing is
determined, and nothing should be. Meanwhile `IsZero`'s `out` must be
determined or the circuit is forgeable. Both used the same keyword.

**The decision.** A third visibility. `private` and `public` are inputs;
`output` is computed and carries the proof obligation. Both `public` and
`output` land in the verifier's public input vector, so nothing changes
cryptographically — the difference is entirely in what the compiler must
prove.

**Consequence.** The determinacy pass has well-defined targets, and circuits
that legitimately determine nothing compile without special-casing.

## Advice need not be determined

The tempting rule is "every advice wire must be pinned down by some
constraint". It is wrong, and rejecting correct code is the way it fails.

In `IsZero`, when `x = 0` the helper `inv` may be *anything*: the constraints
`0 * inv == 1 - out` and `0 * out == 0` say nothing about it. The circuit is
still perfectly sound, because `out` is forced to 1 regardless. A checker
demanding determinacy of `inv` would reject the canonical gadget.

Soundness is about outputs. Advice is a means, not an obligation.

## Why case splitting, rather than a template library

The obvious cheap implementation is to recognise known-good patterns —
`x*inv == 1-out` together with `x*out == 0` is the `IsZero` template — and
whitelist them. Real tooling does some of this.

It was rejected because it does not generalise: a template library can only
bless circuits someone already wrote. The zero/nonzero split plus linear
propagation is a genuine (if small) decision procedure, and it verified
`Divide` without anyone teaching it about division. That is the difference
between a checker and a lookup table.

## Reasoning over F_p, not over the integers

"Is this coefficient nonzero?" is a question about a specific prime. A
coefficient can be a nonzero integer and still vanish modulo p. Reasoning over
`Integer` and hoping would be unsound in exactly the direction that matters.

So the frontend keeps a table of field moduli (`Zkc/Field.hs`) and does its
polynomial arithmetic in the right field. Naming an unknown field is a clean
error listing the known ones — not a silent assumption.

## Running determinacy *after* optimization

Safe, because every pass preserves the solution set of the constraint system:
constant folding and CSE change how a value is computed, never which
assignments satisfy; dead-code elimination only removes nodes no assertion
depends on. Running on the smaller graph keeps the polynomial expansion
cheaper, and the test suite pins the invariant by checking both orders agree.

## Candidate ordering in the proof search

Splitting on the wrong atom still finds a proof, but a worse one. `Divide`
needed three branches when candidates were tried in wire order and two when
*blocking* atoms — those sitting in a coefficient that would otherwise solve
an equation — are tried first. Since the branch count is exponential in depth,
ordering is not cosmetic.

## Failure means "not proved", never "proved unsound"

The analysis is incomplete: bounded depth, bounded polynomial size, and no
handling of degree ≥ 2 in the unknown. It could report failure on a circuit
that is in fact sound.

Because the pass **rejects** on failure, that asymmetry is the safe one:
incompleteness costs expressiveness, not safety. The alternative — accepting
when unsure — would make the entire pass decorative.

This is also why the escape hatch is a language feature (`public` instead of
`output`, stating that a value is an input rather than a computed result)
rather than a `--trust-me` flag. Stating a weaker claim is honest; suppressing
a check is not.

## Soundness inside the artifact

The IR carries the determinacy proof, and the backend refuses to build a
proving key for a circuit that declares outputs without one. A missing record
deserializes to `proved: false`.

The reasoning: "this circuit is sound" is a claim about the circuit, and
artifacts get copied, cached, committed and hand-edited. Checking at the point
of use costs one `if` and closes the gap between what the frontend proved and
what the backend actually proves.

## Errors as a deliverable

An under-constrained circuit is found by reading, so the compiler's output is
part of the product. Every diagnostic carries a source line (echoed with a
gutter), notes explaining the reasoning, and a suggestion. The determinacy
failure names the output, the branch it stays free in, and the advice the
prover may still choose — because "not determined" alone would leave the
author exactly where they started.

## Gadgets are markers, not scopes — for now

Phase-2 `gadget` blocks quarantine advice but do not introduce a scope:
bindings inside remain visible after the block. This is a deliberate
simplification; making them parameterised, reusable definitions is phase-3
work, and doing it properly means call sites, instantiation and per-instance
determinacy obligations. Shipping the quarantine first delivers the safety
property without pretending the module system exists.

---

# Design decisions — phase 4

## The free variables are the atoms, not every wire

The differential-equivalence test (Workstream E.2) first tried to compare R1CS
and Plonkish by perturbing *any* wire of an honest witness and requiring the
two arithmetizations to agree. They did not, and the disagreement was
instructive rather than a bug.

Give a computed wire — say the result of `a * b` — a value inconsistent with
its arguments, and R1CS still accepts while Plonkish rejects. R1CS never reads
that wire: a multiplication constraint recomputes `⟨a,z⟩·⟨b,z⟩` from the
argument variables and compares against `⟨c,z⟩`, and the product wire only
appears as `c` when something downstream forces it. Plonkish, by contrast,
places the product in a witness cell and asserts `a·b - c = 0` on the spot, so
an inconsistent intermediate is caught immediately.

Both are correct encodings of the IR. They merely make a different choice
about where an intermediate value is *defined*: R1CS lets it be implicit in the
recomputation, Plonkish makes it an explicit cell. Neither choice is wrong, and
neither is what a prover controls — the witness solver, which runs on the IR
and is shared by both backends, computes every intermediate from the atoms.

So the variables a prover actually chooses, and the only ones an equivalence
claim should quantify over, are the **atoms**: inputs and advice. Perturb those
and re-solve, keeping the intermediates consistent, and the two arithmetizations
agree without exception. Perturbing a computed wire tests a witness no honest
solver would produce — which is a job for each lowering's own satisfiability
check, not for the equivalence between them.

The general lesson: when two encodings of the same relation disagree, suspect
the comparison before the encodings. Here the encodings were both right and the
comparison was quantifying over the wrong space.
