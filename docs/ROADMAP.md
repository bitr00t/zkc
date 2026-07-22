# Roadmap

A from-scratch zero-knowledge circuit compiler: own language, own
arithmetization, own prover.

Two invariants hold at every phase:

1. **The Core IR is arithmetization-agnostic.** It is a typed constraint
   graph, not an R1CS in disguise, so it can lower to both R1CS and AIR.
2. **Everything is generic over the field.** The field is a parameter, never
   hardcoded — BN254 for Groth16, Goldilocks for the FRI prover later.

| Phase | Content | Status |
|---|---|---|
| 0 | Foundation spike: own field arithmetic, R1CS, satisfiability checker, and a working forgery against an under-constrained circuit | **done** |
| 1 | Walking skeleton: source → typed IR → R1CS → witness → Groth16 proof, end to end | **done** |
| 2 | The type system: `output` vs `public`, advice quarantined in gadgets, determinacy proved by linear propagation + case splitting | **done** |
| 3 | Real IR and optimization: gadgets as parameterised definitions, constraint-count optimization, SMT escalation when the decidable fragment gives up | **done** (see `README_phase3.md`; the gadget stdlib and the Circom benchmark carry over) |
| 4 | Own arithmetization: Plonkish/AIR lowering from the same Core IR | |
| 5 | Own prover: FRI over Goldilocks, replacing arkworks | |
| 6 | Tooling: language server, constraint-count profiler, gadget standard library | |
| 7 | Recursion and formal verification of the lowering | |

## Phase 3 in detail

**Gadgets become definitions.** Parameterised, reusable, with real scopes and
call sites. Each instantiation carries its own determinacy obligation, which
means the proof search must handle obligations compositionally rather than
re-deriving them per circuit.

**SMT escalation.** When the decidable fragment fails, emit the residual
question to an SMT solver over the field rather than rejecting outright. The
decidable core stays the fast path; the solver handles the tail. Crucially the
compiler must then distinguish three outcomes — proved, refuted (with a
counterexample: two witnesses agreeing on inputs and disagreeing on an
output), and unknown — where phase 2 collapses the last two into "rejected".
A refutation is far more useful than a rejection, because it hands the author
the exact attack.

**Constraint-count optimization**, benchmarked against Circom on SHA-256 and
Merkle inclusion. Phase 2's optimizer does constant folding, CSE and dead-code
elimination; competitive lowering needs linear-combination fusion and
multiplication-gate packing.

## Phase 4 in detail

**A second lowering, from the same IR.** Invariant 1 — the Core IR is
arithmetization-agnostic — has never been tested: with one lowering, nothing
would have gone wrong if the IR had quietly grown R1CS-shaped assumptions.
Phase 4 makes the claim falsifiable by lowering the same IR to a **Plonkish**
arithmetization as well, and requires everything upstream (parser, elaborator,
determinacy, optimizer, witness solver) to come through unchanged.

Plonkish rather than a trace-based AIR, because our circuits are combinational
(an AIR's adjacent-row transition constraints want repeated computation, which
the frontend cannot express before phase 6), because a gate graph maps onto
rows and copy constraints directly enough to be obviously faithful, and
because phase 5's FRI-over-Goldilocks prover pairs with Plonkish in
established prior art — so phase 5 replaces the prover without also replacing
the arithmetization.

**The two cost models genuinely disagree**, which is the payoff. R1CS gets
unlimited linear terms free but one multiplication per constraint; a Plonkish
row carries a multiplication *and* linear terms *and* a constant, but sees
only three cells. `IsZero` and `ManyMul` tie; `z == a+b+c+d+e+f` costs 1
constraint against roughly 5 rows. Plonkish therefore needs its own gate
fusion — a different optimization from phase 3's, for a different arithmetic
reason.

**Differential equivalence is what makes it credible.** The same IR and the
same solved witness must satisfy both arithmetizations, and the phase-0
forgery must be rejected by both. Phase 4 stops there — lowered, checked and
measured, with no Plonkish prover — mirroring how R1CS entered in phase 0.

See `docs/phase4.md` for the full design note.
