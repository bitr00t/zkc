# Roadmap

## Invariants every phase must preserve

1. **The Core IR is arithmetization-agnostic** — a typed constraint graph, not
   R1CS with sugar, so it can lower to both R1CS and AIR.
2. **Everything is generic over the field** — BN254 for Groth16, Goldilocks
   for FRI. The field is a parameter, never a hardcoded modulus.

## Phases

- **Phase 0 — foundation & spike.** *(done, see the `zk-phase0` repo)*
  Hand-rolled field arithmetic, an R1CS satisfiability checker, and the
  `IsZero` under-constraining lesson through arkworks Groth16.

- **Phase 1 — walking skeleton.** *(this repo)* Surface language → typed Core
  IR → R1CS → witness → Groth16 proof. Minimal type system, real optimizer
  passes, a versioned IR schema validated on both sides, and the forgery
  reproduced end to end from source.

- **Phase 2 — the type system (the differentiator).** The reason to build this
  compiler rather than use Circom:
  - `Determined<F>` vs `Advice<F>` as real types in the IR, not just a
    frontend check;
  - ordinary users get only `<==` (assign *and* constrain), so their code is
    sound by construction;
  - raw `hint` is quarantined inside `gadget` blocks, each advice wire
    carrying a **determinacy proof obligation**: the assertions must pin the
    value down *uniquely*. Start with a decidable syntactic fragment
    (recognising the standard patterns like `x * inv == 1 - out` together with
    `x * out == 0`), escalate to an SMT solver for the rest;
  - public/private information-flow labels, and automatic range checks.
  Success criterion: `examples/iszero_broken.zkc` becomes a compile error with
  a message that explains *which* value is not determined and why.

- **Phase 3 — real IR & optimizations.** Constraint minimization, better CSE,
  witness scheduling, multiplication-by-constant folded into linear
  combinations. Benchmark constraint counts against Circom on SHA-256 and a
  Merkle path — a number, not a claim.

- **Phase 4 — own arithmetization.** R1CS → Plonkish (custom gates + lookup
  arguments), or commit to AIR directly.

- **Phase 5 — own prover.** Field NTT, a commitment scheme, FRI, the
  polynomial IOP, prover and verifier. FRI/STARK to avoid pairings and a
  trusted setup: only field and Merkle math, which is safe to implement
  yourself.

- **Phase 6 — tooling & ecosystem.** LSP, formatter, stdlib (Poseidon, Merkle,
  ECDSA), Solidity verifier codegen, docs. This is what drives adoption.

- **Phase 7 — stretch.** Recursion / proof composition, a zkVM frontend,
  formal verification of the lowering passes.

## Immediate next steps for phase 2

1. Put wire kinds into the IR schema (version bump to 2).
2. Add `gadget` blocks to the grammar; make bare `hint` outside a gadget an
   error.
3. Implement the determinacy pass over the decidable fragment, with the
   `IsZero` pattern as the first recognised template.
4. Turn `iszero_broken.zkc` into a compile-error test case, and keep a
   `gadget`-wrapped version that still compiles as the escape hatch.
