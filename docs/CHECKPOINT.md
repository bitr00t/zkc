# zkc — project checkpoint

*A resume-from-here snapshot: where the project stands, what was decided and
why, what is deliberately unfinished, and what to do next. Written so a fresh
session (or a fresh reader) can pick up without the conversation history.*

Repository: `bitr00t/zkc`. Frontend in Haskell, backend in Rust.

---

## 1. What the project is

`zkc` is a from-scratch zero-knowledge circuit compiler. Its thesis, and the
thing that makes it more than a re-implementation, is a **determinacy type
system**: a circuit whose outputs are not uniquely determined by its inputs is
a **compile error**, not a runtime surprise. Under-constrained circuits — the
classic, catastrophic ZK bug — are caught statically.

Two invariants hold the architecture together and have been maintained since the
early phases:

1. **The Core IR is arithmetization-agnostic.** It is a typed constraint graph,
   not an R1CS in disguise. Proven by lowering the *same* IR two independent
   ways (R1CS and Plonkish) with identical results.
2. **Everything is generic over the field**, via the `ZkField` trait. Proven by
   running the existing lowerings over a hand-written Goldilocks field with
   identical constraint counts to BN254.

The recurring proof-of-work throughout is a specific bug — the **"phase-0
forgery"**: the `IsZero` circuit with `inv` overridden to 0, `x=5`, `out=1`,
which satisfies one assertion while claiming a false output. Every layer added
(SMT, Plonkish, the STARK) is tested to reject it.

---

## 2. Implementation progress

| Phase | Scope | Status |
|---|---|---|
| 0–2 | Frontend, determinacy type system, R1CS, borrowed Groth16 prover | **done** (prior) |
| 3 | Gadgets, SMT escalation, constraint fusion | **done** |
| 4 | Own arithmetization: Plonkish from the same IR | **done** |
| 5 | Own prover: FRI/STARK over Goldilocks, retiring arkworks | **done** |
| 6 | Tooling: language server, profiler, gadget stdlib | **designed, not implemented** |
| 7 | Recursion + formal verification of the lowering | not started |

**Test status: 81 backend tests, 90/90 frontend checks, all green, zero warnings.**

### Phase 3 — done
- **A (gadgets):** parameterised gadget definitions with compositional
  determinacy; `gadget name(p: field) -> (r: field) { require ...; }`; proven
  once per gadget, summary applied at each instance.
- **B (SMT escalation):** three-valued determinacy `Proved | Refuted | Unknown`.
  `compiler/src/Zkc/Analysis/Smt.hs`. Query = uniqueness-as-self-composition
  (two witnesses, same inputs — can an output differ? unsat = proved, sat =
  forgery). Refutation prints the actual forged witness. Flags: `--no-smt`
  (exact phase-2 behaviour), `--smt-solver`, `--smt-dialect ff|int`,
  `--smt-timeout`, `--dump-smt`.
- **C (fusion + benchmark):** multiplicative-assertion fusion in the R1CS
  lowering (`assert a*b==c` → 1 constraint instead of 2). `lower_with(ir, fuse)`.
  Measured 50% reduction on `ManyProducts` n=64.

### Phase 4 — done (`docs/README_phase4.md`)
- **D (Plonkish):** `backend/zkc-core/src/plonkish.rs`. Rows with 5 selectors +
  3 cells, gate identity `q_L·a + q_R·b + q_O·c + q_M·a·b + q_C = 0`, copy
  constraints as explicit wiring. Gate fusion hits targets: IsZero 7→2, ManyMul
  16→8, WideSum 6→5.
- **E (validation + equivalence):** `validate()` checks the lowering is
  well-formed (catches unwired sharing, selectors on empty cells).
  `verdicts_agree` — R1CS and Plonkish reach the same verdict on the same
  witness. **Key finding:** free variables are *atoms* (inputs+advice), not
  computed wires; the witness solver is the arbiter of intermediates.
- **F (cost + CLI):** `zkc-stats` binary reports both arithmetizations'
  costs side by side. `zkc-prove --arith r1cs|plonkish`; the determinacy record
  travels identically on both paths.

### Phase 5 — done (`docs/README_phase5.md`, `docs/phase5-status.md`)
- **G (field + FFT):** hand-written `goldilocks.rs` (`p = 2^64 - 2^32 + 1`,
  fast reduction, Fermat inverse), differentially tested against arkworks on
  50k+ inputs. `fft.rs` — NTT/iNTT/coset-LDE over a `TwoAdicField` trait.
- **H (commitment + transcript):** `Hasher` trait (`hash.rs`), `merkle.rs`
  commitment with tamper tests, `transcript.rs` Fiat–Shamir.
- **I (the STARK):** `air.rs` (Plonkish → polynomial gate constraint + σ
  permutation), `fri.rs` (low-degree test), `stark.rs` (commit trace, form
  quotient, FRI, consistency check). **Includes the grand-product permutation
  argument** for full wiring soundness — a broken wire is rejected.
- End-to-end: honest witness proves and verifies; phase-0 forgery yields no
  accepted proof; arkworks gone from the proving path.

### Phase 6 — designed only (`docs/phase6.md`)
Four workstreams (J, K, L, M) — see §5.

---

## 3. Key decisions

- **Determinacy as uniqueness-as-self-composition** (phase 3B): ask the solver
  whether two witnesses sharing inputs can differ on an output. Clean, and it
  gives a real forged witness on failure.
- **SMT soundness asymmetry** (phase 3B): a scope that includes proven gadget
  summaries is a *relaxation*, so `unsat` (a proof) carries over safely, but
  `sat` (an apparent forgery) is downgraded to `Unknown` rather than trusted.
- **Plonkish, not trace-AIR** (phase 4): circuits are combinational; the gate
  graph maps to rows + copy constraints. This choice is what made phase 5
  tractable — a STARK proves a Plonkish table almost directly.
- **Free variables are atoms** (phase 4E): the equivalence between
  arithmetizations quantifies over inputs and advice only; computed wires are
  fixed by the shared witness solver. Found by a differential test that first
  failed — the encodings were both right and the *comparison* was wrong.
- **Field hand-written, hash borrowed, FRI hand-written** (phase 5): the hash
  is the single most security-critical component, so it lives behind a `Hasher`
  trait and is instantiated (eventually) with a reviewed arithmetic hash; the
  field and FRI are the point of the phase and are built in-house.
- **The gate constraint alone catches the forgery** (phase 5I): the phase-0
  forgery is a *gate* violation, so it is rejected even without the permutation
  argument — which is why the wiring argument could be layered on afterward
  without weakening the core security claim.
- **Phase 6 breaks the "frontend untouched" invariant, honestly** (phase 6):
  tooling *is* frontend work. The replacement discipline: every frontend change
  is additive and regression-tested against the 90 frontend checks; the
  determinacy analysis is *surfaced*, not recomputed.

---

## 4. Open issues and explicit boundaries

These are deliberately unfinished and marked as such — not bugs, but scoped-out
work.

- **Phase 5 — DEEP / FRI-batch (the one soundness boundary).** FRI proves the
  composite *quotient* is low-degree. The committed trace and grand-product `Z`
  columns are opened for the consistency check but not themselves folded into
  the low-degree test. Binding them (the standard DEEP step) is the remaining
  hardening for full arithmetic soundness against a prover who commits
  non-polynomial columns. Does not affect the honest / forgery / wiring results.
- **Phase 5 — the hash is a stand-in.** Tests use `ToyHash` (an `x^7`
  permutation), explicitly not vetted. Swapping in a reviewed Poseidon or
  Rescue-Prime over Goldilocks is a *leaf change* — everything is written
  against the `Hasher` trait — but it is not done.
- **Phase 3 C.2 — full SHA-256/Merkle benchmark blocked.** Needs intermediate
  composition (fresh non-output result wires) that was deferred, and Circom (for
  cross-comparison) is unavailable in the build environment.
- **SMT — cvc5 cannot solve finite-field queries.** The cvc5 build available
  has no CoCoA backend, so `QF_FF` queries are only syntactically verified,
  never solved. z3 4.8.12 works for the `QF_NIA` (integer-mod) dialect, which is
  what the refutation tests actually run against.
- **Toolchain — committed `Cargo.lock` needs local downgrades on cargo 1.75.**
  The committed lock pulls edition-2024 transitive deps that need rustc ≥ 1.80.
  Building on the environment's cargo 1.75 requires local downgrades (see §6);
  these are **applied locally only and never committed to deliverables** — the
  committed pins are left untouched.

---

## 5. Next steps

The clear next unit of work is **Phase 6 implementation**, and within it the
order is fixed by dependency: **J → (K, L in parallel) → M.**

**Start with J.1 — JSON diagnostics.** It is the smallest, most isolated, most
testable frontend change, and everything else in the phase depends on structured
diagnostics existing. Concretely: add a JSON emitter beside the existing
`render` in `compiler/src/Zkc/Diagnostics.hs`, serialising the existing
`Diagnostic { message, line, notes, help }` record. Round-trip test every
existing diagnostic kind (determinacy failure, refutation, residual) through it.
This touches the frontend but is purely additive — the regression bar is the
existing 90 frontend checks staying green.

Then:
- **J.2** — thread columns through the lexer (it already walks characters) and
  spans through the AST, only where diagnostics land (outputs, assertions,
  gadget calls).
- **K** — an LSP server (Haskell, reusing the compiler as a library) publishing
  determinacy diagnostics; then hovers/lenses surfacing the `--explain` proof.
- **L** — per-source-line cost attribution via the lowering's `origin` strings,
  as a `zkc-profile` report and editor inlay hints. Sums must match `zkc-stats`.
- **M** — a `std/` of gadgets written in `.zkc`, each proved determinate by the
  same analysis (with a negative fixture each), plus an include mechanism.

**Alternative**, if hardening is preferred over new features: finish the two
phase-5 boundaries (DEEP batch; real hash). Both are well-defined and neither is
a redesign.

---

## 6. How to build and test (environment notes)

**Frontend (Haskell, GHC 9.4.7):**
```
make -C compiler all                       # → compiler/build/zkc
# tests:
ghc -O0 -isrc -itests -outputdir build/test-objs -o build/spec tests/Spec.hs && ./build/spec
```

**Backend (Rust, cargo/rustc 1.75.0):**
```
cd backend && cargo test                   # all tests
cargo build --bin zkc-stats                # cost profiler (phase 4)
cargo build --bin zkc-prove                # Groth16 + --arith path
```

**Recurring toolchain fix** (local only, do NOT commit — the committed
`Cargo.lock` pins are intentional):
```
cargo update -p zeroize --precise 1.8.1
cargo update -p zeroize_derive --precise 1.4.2
# for the arkworks chain in zkc-prove additionally:
cargo update -p rayon --precise 1.10.0
cargo update -p rayon-core --precise 1.12.1
```
`zkc-core` builds standalone (only serde / serde_json / ark-ff) once `zeroize`
is downgraded; `zkc-prove` (arkworks/Groth16) also needs the `rayon` downgrades.

**SMT:** z3 4.8.12 (works, `QF_NIA`). cvc5 1.3.4 available but no CoCoA (cannot
solve `QF_FF`).

---

## 7. Repository map

```
compiler/                        Haskell frontend
  src/Main.hs                    CLI: --explain, --no-smt, --smt-*, --dump-smt
  src/Zkc/
    Syntax/{Lexer,Parser,Ast}.hs lexer tags tokLine; AST carries pdLine/gdLine
    Analysis/{Determinacy,Smt}.hs the type system + SMT escalation
    Core/, Emit/                 elaboration, IR emission
    Field.hs, Diagnostics.hs     Diagnostic{message,line,notes,help}, render
  examples/*.zkc                 iszero, divide, mul_square, relation, ...
  tests/Spec.hs                  90 frontend checks

backend/
  zkc-core/                      kryptographiefrei; generic over ZkField
    src/ir.rs                    the neutral Core IR (carries determinacy record)
    src/field.rs                 ZkField + TwoAdicField traits
    src/lower.rs, r1cs.rs        R1CS lowering + fusion
    src/plonkish.rs              Plonkish lowering + gate fusion + validate
    src/witness.rs               witness solver (arbiter of intermediates)
    src/goldilocks.rs            hand-written field (phase 5)
    src/fft.rs                   NTT/iNTT/coset-LDE
    src/hash.rs, merkle.rs, transcript.rs   commitment + Fiat–Shamir
    src/air.rs, fri.rs, stark.rs the STARK (gate constraint + permutation)
    tests/                       core, goldilocks, fft, commitment, fri, stark
  zkc-prove/                     arkworks Groth16 (borrowed; being retired)
    src/bin/zkc-prove.rs         --arith r1cs|plonkish
    src/bin/zkc-stats.rs         cost comparison

docs/
  ROADMAP.md                     the 7-phase plan + per-phase detail
  DESIGN_DECISIONS.md            recorded rationale
  phase4.md, phase5.md, phase5-status.md, phase6.md
  benchmarks.md                  cost tables + STARK-vs-Groth16 numbers
  CHECKPOINT.md                  this file
```

---

## 8. Headline numbers (for reference)

**Phase 4 — arithmetization cost (fused):** R1CS and Plonkish *tie* on
multiplication-shaped circuits (IsZero 2/2, ManyMul 8/8); R1CS wins on a wide
linear sum (WideSum 1 vs 5). Neither dominates — which is what justifies the
neutral IR.

**Phase 5 — STARK vs Groth16 (IsZero, honest witness):**

| | Groth16 (BN254) | zkc STARK (Goldilocks) |
|---|---|---|
| proof size | 128 bytes | ~25,000 bytes |
| prover time | 21.7 ms | 1.1 ms |
| verifier time | 58.9 ms | 2.0 ms |
| trusted setup | required | none |

The textbook trade: Groth16 keeps a large proof-size edge; the STARK needs no
trusted setup, trusts only a hash, and is faster on small circuits. (Caveats:
tiny-circuit timings favour the STARK; its proof size is inflated by the
stand-in hash and an unoptimised opening format.)
