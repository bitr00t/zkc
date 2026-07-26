# Phase 7 — Recursion and formal verification of the lowering

The roadmap's last phase has two halves. One looks *down*: the lowering from
Core IR to the two arithmetizations has been trusted since phase 1 and
differential-tested since phase 4, but never checked against an independent
statement of what the IR *means*. The other looks *up*: a proof has so far been
the end of the line — nothing consumes one. Phase 7 makes the lowering
*verified* rather than merely tested, and makes a proof into something a circuit
can check, so proofs can compose.

Both halves inherit the project's two standing invariants, and neither is
allowed to break them:

1. **The Core IR is arithmetization-agnostic.** The specification written in
   this phase is a statement about the IR, not about R1CS or Plonkish, and both
   lowerings are measured against it.
2. **Everything is generic over the field.** The spec, the per-rule checks, and
   the verifier gadgets are written over `ZkField`; only the recursion leaf that
   touches a concrete proof system may name a concrete field.

The discipline that phase 6 adopted — every change additive and
regression-tested — continues. Nothing in the determinacy analysis, the SMT
layer, the witness solver, or the two lowerings changes behaviour; the phase-0
forgery is still rejected end to end.

## N — Formal verification of the lowering

The lowering has been checked *differentially*: phase 4 proved that R1CS and
Plonkish agree with **each other** on the honest witness, the phase-0 forgery,
and random perturbations. That is a strong test with one blind spot — two
lowerings that were wrong in the *same* way would agree, and the test would pass.
The blind spot exists because there was no third party: no statement of what the
IR means that is independent of how it is lowered.

**N.1 — An executable specification of the IR.** Give IR satisfaction a
definition that names no arithmetization: the constant-one wire holds 1, every
arithmetic node equals its operation applied to its arguments, every assertion
holds, and a *hint* node is unconstrained — its wire is a value the prover
chooses, which is precisely the freedom the determinacy type system exists to
discipline. This is the specification the lowerings are verified against. Tested
by *three-way* agreement — spec ⟺ R1CS ⟺ Plonkish — on solved witnesses and on
random perturbations of the atoms (inputs and advice), and by the spec
independently rejecting the phase-0 forgery on the correct circuit. Where phase
4 locked two arithmetizations together, N.1 pins both to a truth outside either.

**N.2 — Per-rule faithfulness, proved rather than sampled.** N.1 tests the
lowering on assignments; N.2 proves the *rules*. For each lowering rule — each
IR operation and the constraints or rows it emits — show the emitted system is
equisatisfiable with the operation's defining relation *for every field
element*, not merely on sampled witnesses. The machinery already exists: phase
3's SMT layer proves equisatisfiability of polynomial systems over F_p, and the
same self-composition question ("can two assignments agree on the inputs and
differ on the output?") applies to a single lowered rule. Rules small enough to
settle by exhaustive evaluation over a tiny field are checked that way; the rest
go to the solver. A rule that cannot be shown equisatisfiable is a lowering bug,
reported as one.

**N.3 — A checker with teeth.** A specification is only worth as much as its
ability to fail. N.3 is a mutation harness: deliberately corrupt each lowering
rule (drop a constraint, flip a sign, misroute a copy constraint) and confirm
that N.1's three-way agreement breaks — so the verification is demonstrably not
vacuous. A rule whose corruption still passes is a hole in the spec, not a
success.

## O — Recursion

A proof about a proof. Today a proof is produced and verified and that is the
end of it; recursion makes "this proof verifies" a statement a circuit can
assert, which is what aggregation, rollups, and incrementally-verifiable
computation are all built on.

**O.1 — A verifier, in the language.** Express the checks a verifier performs —
the Fiat–Shamir transcript, Merkle-path openings, the FRI folding relations, the
gate and permutation identities — as gadgets in the zkc language. Written this
way, "the proof verifies" is an ordinary circuit, held to the same determinacy
proof as any other: the verifier's own advice is quarantined and its outputs
must be determined by the proof and verification key it is handed.

**O.2 — Recursive composition.** Feed a proof and its verification key as inputs
to the verifier circuit and prove *that* circuit's execution — one proof
attesting to another's validity. The milestone is the smallest honest recursion:
a phase-5 proof of a small circuit, verified inside a second proof, with the
security test that matches every prior phase — a tampered inner proof makes the
outer proof fail to build or verify.

**Order: N → O.** N is the groundwork: recursion trusts the lowering more than
anything else in the system, because a verifier circuit's soundness rests on the
lowering being faithful. Verify the lowering first, then build the thing that
leans hardest on it. Within N, the order is N.1 → N.2 → N.3 (a spec, then proofs
about the rules, then evidence the spec can fail). O.1 → O.2 (a verifier, then a
proof that runs it).

## What it costs to the invariants

- **Arithmetization-agnostic IR.** N.1's spec is defined on the IR alone; it
  mentions neither lowering, and is the arbiter *between* them. This
  strengthens the invariant rather than straining it.
- **Generic over the field.** N.1–N.3 are `ZkField`-generic. O is where a
  concrete proof system finally appears, and the discipline mirrors phase 5's:
  the field-specific verifier arithmetic is a *leaf*, hung under gadget
  interfaces the rest of the language already speaks; the recursion machinery
  around it stays generic.

## Scope, drawn on purpose

- **Verification means equisatisfiability of the lowering, not a proof-assistant
  development.** The project's rigor is executable specifications, SMT, and
  differential checks — not Coq or Lean. N verifies that *our* lowering
  implements *our* IR semantics. Proving the FRI prover cryptographically sound
  is the literature's domain and stays out of scope.
- **One verifier, and the smallest honest recursion.** O delivers a single
  verifier and one proof-inside-a-proof. Production accumulation schemes (folding,
  Nova-style IVC) are downstream engineering, not the phase that proves the model.
- **No new field or prover.** Phase 5's FRI/Goldilocks prover is reused; O adds a
  consumer of proofs, not a new producer.

## What "done" looks like

1. An executable IR specification, with three-way agreement (spec ⟺ R1CS ⟺
   Plonkish) property-tested on witnesses and random perturbations.
2. Per-rule faithfulness shown equisatisfiable over the field, by exhaustion or
   by the SMT layer.
3. A mutation harness demonstrating the specification catches a broken lowering.
4. A verifier expressed in the language and held to the determinacy proof.
5. One proof verified inside another; a tampered inner proof fails.
6. **Every addition additive** — determinacy, SMT, witness solving, and both
   lowerings unchanged, and the phase-0 forgery still rejected end to end.
