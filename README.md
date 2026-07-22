# Phase 4 — own arithmetization

> Design note. Decisions are marked and can be overridden; the numbers in
> "What it costs" are measured, not assumed.

## What this phase is actually for

Invariant 1 says the Core IR is arithmetization-agnostic — "a typed constraint
graph, not an R1CS in disguise". Through phase 3 that claim has never been
tested. There is exactly one lowering, so nothing would have gone wrong if the
IR had quietly grown R1CS-shaped assumptions. An untested invariant is a
hope.

Phase 4 adds a **second lowering from the same IR** and makes the two coexist.
That is the whole point: not "we support Plonkish now" but "the neutrality
claim is now falsifiable, and it survived". Everything upstream of the
lowering — parser, elaborator, determinacy, optimizer, witness solver — must
come through **completely unchanged**. If any of it needs a patch, we have
found a genuine architectural defect, and finding it is a success too.

## Decision: Plonkish, not a trace-based AIR

The roadmap says "Plonkish/AIR". These are different targets and the choice
matters, so: **Plonkish**, for three reasons.

**Our circuits are combinational.** A trace-based AIR expresses constraints
between *adjacent rows* of an execution trace — it is built for repeated
computation (VM cycles, hash rounds), where one transition constraint covers
thousands of steps. A combinational circuit has no time axis to repeat over,
so lowering it to an AIR degenerates: every row is different and the
transition constraint has to be a giant disjunction, or you pad to a trace
that is mostly selector plumbing. AIR becomes the right target when the
frontend can express loops, which is not before phase 6.

**Plonkish is the natural second arithmetization for a gate graph.** Each IR
node becomes a row, wiring becomes copy constraints. The mapping is direct
enough to be obviously faithful, which is what we need for a differential
test to mean something.

**It is what phase 5 wants.** Phase 5 is FRI over Goldilocks. The
best-established design in exactly that space — Plonkish arithmetization,
FRI, Goldilocks — already exists as prior art (Plonky2), so choosing
Plonkish now means phase 5 replaces the prover without also replacing the
arithmetization. Choosing AIR would put a second rewrite between here and a
working FRI prover.

*Overridable:* if the goal is to prepare a zkVM rather than a circuit
compiler, AIR is the better bet and this decision flips.

## What it costs — measured, and the reason it is interesting

The two arithmetizations have genuinely different bills, which is the payoff
of keeping the IR neutral. The trade is sharp:

* **R1CS** — a constraint is `⟨a,w⟩·⟨b,w⟩ = ⟨c,w⟩`. Unlimited linear terms
  are *free* (they fold into a linear combination); exactly **one
  multiplication** per constraint.
* **Plonkish** — a row is `q_L·a + q_R·b + q_O·c + q_M·a·b + q_C = 0`. It
  holds a multiplication *and* linear terms *and* a constant at once, but it
  sees only **three cells**.

So each wins where the other is weak. Measured on circuits already in the
repo (R1CS numbers from the backend; Plonkish projected from the gate shape):

| circuit | shape | R1CS | Plonkish |
|---|---|---|---|
| `IsZero` | 2 mul, 1 linear, 2 assertions | 2 | 2 |
| `ManyMul` | 8 independent products | 8 | 8 |
| `WideSum` | `z == a+b+c+d+e+f` | **1** | **~5** |

`WideSum` is the honest discriminator: six summands fold into a single R1CS
linear combination, but a three-cell gate has to chain them across rows.
Conversely Plonkish gains where R1CS cannot follow at all — custom gates that
verify a whole hash round in one row — though that only pays off once the
gadget standard library exists.

Two consequences worth stating now. First, **a naive node-per-row lowering is
about twice as expensive as R1CS** on our examples, so Plonkish needs its own
fusion, and it is a *different* fusion from Workstream C's: C folded a
multiplication into an assertion because R1CS has a spare product slot;
Plonkish folds because a gate has spare linear slots. Same IR, same intent,
different arithmetic reason. Second, the compiler will for the first time be
able to answer "which arithmetization is cheaper for *this* circuit" with a
number instead of a preference.

## Workstreams

### D — The Plonkish arithmetization

**D.1 — Target and lowering.** A `plonkish.rs` in `zkc-core`, parallel to
`r1cs.rs`: witness columns `a, b, c`, selector columns `q_L, q_R, q_O, q_M,
q_C`, rows, and an explicit set of **copy constraints** (cell ≡ cell) standing
in for the permutation argument. Then `lower_plonkish(&Ir) -> Plonkish<F>`
from the same `Ir` the R1CS lowering consumes. Generic over the field, as
everything in this crate is.

**D.2 — Gate fusion.** The Plonkish-native cost optimization: fold each
assertion, and the multiplication or linear terms feeding it, into as few rows
as the three-cell budget allows. Reported against an unfused baseline, exactly
as Workstream C did, so the win is a measured delta.

### E — Trust: checking and differential equivalence

**E.1 — Satisfiability and well-formedness.** *Done.* Two checks, not one.
`Plonkish::is_satisfied(assignment)` is the analogue of `R1cs::is_satisfied`:
every gate identity holds, and every copy constraint relates two cells that
actually agree. But that only answers "does this witness satisfy the circuit",
and a lowering bug that wired nothing together would pass it on the honest
witness while being silently unsound. So `Plonkish::validate()` answers the
prior question — "is this a well-formed circuit at all" — with no witness in
sight: selectors match their cells, every shared wire's occurrences are a
single connected component under the copy relation, and every public input
reaches a cell. The wiring check is the one that matters, and two tests break
a real lowering (drop a copy constraint; switch on a selector over an empty
cell) and require the break to be caught, because a validator that only ever
passes is decoration. Violations describe themselves in source terms, as the
R1CS checker does.

**E.2 — Differential equivalence.** *Done.* The centrepiece: two independently
written lowerings must encode the **same statement**, not merely both be
satisfiable somewhere. For the same IR and the same solved witness — the
witness solver runs on the IR and is shared unchanged, so "same witness" is
literal, not approximate — the verdicts must agree assignment by assignment.
Checked where it matters (the honest witness, accepted by both; the phase-0
forgery, rejected by both; the broken circuit, under-constrained in both) and
then stress-tested with 1200 random consistent witnesses across four circuits.

The random test **found something**, which is the point of differential
testing. Perturbing a *computed* wire to a value inconsistent with its inputs
splits the two: R1CS never reads such a wire (it recomputes `a·b` from the
argument cells), while Plonkish places the product in a cell and checks
`a·b - c = 0`, so it catches the inconsistency. Both lowerings are correct;
they encode "the solver already computed the intermediates" differently. The
resolution is that the free variables are the **atoms** — inputs and advice —
because the shared witness solver, not the assignment, is the arbiter of every
intermediate value. Perturb the atoms and re-solve, and the two agree without
exception. (See DESIGN_DECISIONS.)

### F — The payoff: measuring neutrality

**F.1 — Cost comparison.** Extend the benchmark harness to report both bills
per circuit — R1CS constraints/variables against Plonkish rows/columns —
including the crossover cases above. This is the invariant paying rent.

**F.2 — Selecting an arithmetization.** A `--arith r1cs|plonkish` path through
the CLI and the emitted artifact, so a circuit can actually be built either
way. The determinacy record travels unchanged: soundness is a property of the
IR, not of how it is arithmetized, and that is worth demonstrating rather than
asserting.

**Order: D → E → F.** E cannot precede D, and F needs both. E should not be
deferred — an unchecked second lowering is worth less than no second lowering,
because it invites trust it has not earned.

## Scope, drawn on purpose

- **No Plonkish prover.** Phase 4 stops at lowered, checked, and measured —
  mirroring how R1CS entered in phase 0, a satisfiability checker before any
  cryptography. Proving is phase 5.
- **Copy constraints are checked, not argued.** A real Plonk prover enforces
  them with a permutation polynomial and a grand-product argument. Here they
  are an explicit relation, verified directly. Building the permutation
  argument is prover work.
- **Generic gate only.** Custom gates are where Plonkish decisively beats
  R1CS, but they only pay for circuits like hash rounds, which need the gadget
  standard library still carried over from phase 3.
- **Field stays a parameter.** Testing continues on BN254; the concrete
  Goldilocks implementation arrives with phase 5's prover, against the same
  `ZkField` trait.
- **The frontend does not change.** If it turns out it must, that is a finding
  to report, not a patch to slip in.

## What "done" looks like

1. The same IR lowers to R1CS and to Plonkish, both checkable.
2. An honest witness satisfies both; the phase-0 forgery is rejected by both.
3. Fusion reduces Plonkish rows by a measured amount.
4. A cost table showing where the two arithmetizations disagree.
5. **Not one line of the frontend changed.**
