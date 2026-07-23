# Roadmap

A from-scratch zero-knowledge circuit compiler: own language, own
arithmetization, own prover.

Two invariants hold at every phase:

1. **The Core IR is arithmetization-agnostic.** It is a typed constraint
   graph, not an R1CS in disguise, so it can lower to both R1CS and AIR.
2. **Everything is generic over the field.** The field is a parameter, never
   hardcoded — BN254 for Groth16, Goldilocks for the FRI prover later.

| Phase | Content                                                                                                                                            | Status                                                                                           |
| ----- | -------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------ |
| 0     | Foundation spike: own field arithmetic, R1CS, satisfiability checker, and a working forgery against an under-constrained circuit                   | **done**                                                                                   |
| 1     | Walking skeleton: source → typed IR → R1CS → witness → Groth16 proof, end to end                                                               | **done**                                                                                   |
| 2     | The type system:`output` vs `public`, advice quarantined in gadgets, determinacy proved by linear propagation + case splitting                 | **done**                                                                                   |
| 3     | Real IR and optimization: gadgets as parameterised definitions, constraint-count optimization, SMT escalation when the decidable fragment gives up | **done** (see `README_phase3.md`; the gadget stdlib and the Circom benchmark carry over) |
| 4     | Own arithmetization: Plonkish/AIR lowering from the same Core IR                                                                                   | **done** (see `docs/README_phase4.md`)                                                          |
| 5     | Own prover: FRI over Goldilocks, replacing arkworks                                                                                                | **done** (see `docs/README_phase5.md`, `docs/phase5-status.md`)                               |
| 6     | Tooling: language server, constraint-count profiler, gadget standard library                                                                       |                                                                                                  |
| 7     | Recursion and formal verification of the lowering                                                                                                  |                                                                                                  |

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

See `docs/README_phase3.md` for the full design note.

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

See `docs/README_phase4.md` for the full design note.

## Phase 5 in detail

**A hand-written FRI/STARK prover over Goldilocks, replacing arkworks.** A
STARK wants the opposite field from the pairing-based Groth16 borrowed so far:
not a ~254-bit pairing-friendly field but a small, high-two-adicity one, so its
FFTs are cheap. Goldilocks (`2^64 - 2^32 + 1`) fits in a machine word and has
`2^32 | p - 1`.

The whole backend has been generic over `ZkField` since phase 1 for exactly
this. Before designing the phase, that was tested: instantiating the existing
lowerings over Goldilocks instead of BN254 compiles and produces identical
constraint counts, so the frontend, both lowerings, the witness solver and the
checkers are already field-agnostic in fact. **The new work is a leaf** — a
field and a prover hung under an interface everything else already speaks.

Phase 4's Plonkish is why this is tractable: a STARK proves a table of rows
with a gate identity and a permutation argument almost directly, which is what
Plonkish already is. The pieces that are genuinely new are the small field
(G), an FFT/LDE and Merkle+Fiat–Shamir commitment (G/H), and FRI itself (I).
The hash is borrowed from a reviewed crate at first — a hand-rolled hash is the
last thing that should go unaudited — while the field and FRI are hand-written,
because they are the point. The end-to-end security test is the familiar one:
the honest witness proves and verifies, the phase-0 forgery does not.

See `docs/README_phase5.md` for the full design note.

## Phase 6 in detail

**Tooling: a language server, a constraint-count profiler, and a gadget
standard library.** This is the phase where the determinacy type system — the
project's thesis — stops being a compiler feature and becomes a working
environment. A proof that an output is under-determined is worth far more as a
red underline the moment it is typed than as a terminal line after a full build.

It is also the phase where the "not one line of the frontend changed" invariant
retires, honestly rather than by redefinition: **tooling for a language is
frontend work.** The shaping measurement was what the frontend already supports.
It tracks lines end to end (lexer, AST, IR, diagnostics) but not columns; its
diagnostics are already a structured record but are rendered only to strings;
gadgets exist but there is no library; `zkc-stats` emits JSON but not per-line
cost. So the frontend changes are additive and narrow — a JSON emitter beside
the renderer, columns beside lines, an include for library gadgets — and the
determinacy analysis is *surfaced*, not recomputed.

Workstreams: **J** (machine-readable JSON diagnostics and column spans — the
groundwork), **K** (the LSP server, wrapping the real pipeline, with hovers and
lenses that show *why* an output is determined), **L** (per-source-line cost
attribution over phase 4's cost model and phase 5's measurements, as a report
and editor inlay hints), and **M** (a small standard library of gadgets written
in the language and held to the same determinacy proof as user code — even the
library is checked, not trusted). The invariant that replaces "frontend
untouched" is that every frontend change is additive and regression-tested
against the existing 90 frontend checks.

See `docs/phase6.md` for the full design note.
