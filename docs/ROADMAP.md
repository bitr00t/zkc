# Roadmap

A from-scratch zero-knowledge circuit compiler: own language, own
arithmetization, own prover.

Two invariants hold at every phase:

1. **The Core IR is arithmetization-agnostic.** It is a typed constraint
   graph, not an R1CS in disguise, so it can lower to both R1CS and AIR.
2. **Everything is generic over the field.** The field is a parameter, never
   hardcoded — BN254 for Groth16, Goldilocks for the FRI prover later.

| Phase | Content                                                                                                                                            | Status                                                                                    |
| ----- | -------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| 0     | Foundation spike: own field arithmetic, R1CS, satisfiability checker, and a working forgery against an under-constrained circuit                   | **done**                                                                            |
| 1     | Walking skeleton: source → typed IR → R1CS → witness → Groth16 proof, end to end                                                               | **done**                                                                            |
| 2     | The type system:`output` vs `public`, advice quarantined in gadgets, determinacy proved by linear propagation + case splitting                 | **done**                                                                            |
| 3     | Real IR and optimization: gadgets as parameterised definitions, constraint-count optimization, SMT escalation when the decidable fragment gives up | **done** (see `README.md`; the gadget stdlib and the Circom benchmark carry over) |
| 4     | Own arithmetization: Plonkish/AIR lowering from the same Core IR                                                                                   |                                                                                           |
| 5     | Own prover: FRI over Goldilocks, replacing arkworks                                                                                                |                                                                                           |
| 6     | Tooling: language server, constraint-count profiler, gadget standard library                                                                       |                                                                                           |
| 7     | Recursion and formal verification of the lowering                                                                                                  |                                                                                           |

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
