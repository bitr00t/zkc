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
   running the lowerings over a hand-written Goldilocks field with identical
   constraint counts to BN254.

The recurring proof-of-work throughout is a specific bug — the **"phase-0
forgery"**: the `IsZero` circuit with `inv` overridden to 0, `x=5`, `out=1`,
which satisfies one assertion while claiming a false output. Every layer added
(SMT, Plonkish, the STARK, the recursion work) is tested to reject it.

---

## 2. Implementation progress

**All seven roadmap phases are done.** The roadmap is complete; work now is
hardening the two remaining soundness boundaries and building on the phase-7
primitives.

| Phase | Scope | Status |
|---|---|---|
| 0–2 | Frontend, determinacy type system, R1CS, borrowed Groth16 prover | **done** |
| 3 | Gadgets, SMT escalation, constraint fusion | **done** |
| 4 | Own arithmetization: Plonkish from the same IR | **done** |
| 5 | Own prover: FRI/STARK over Goldilocks, retiring arkworks | **done** |
| 6 | Tooling: language server, profiler, gadget stdlib | **done** |
| 7 | Recursion + formal verification of the lowering | **done** |

**Test status: 135 backend tests, 172/172 frontend checks, all green, zero
warnings.**

### Phase 6 — done
- **J (structured diagnostics):** JSON diagnostics beside the human `render`
  (`Diagnose.hs`, `Json.hs`), columns through the lexer and spans through the
  AST where diagnostics land.
- **K (language server):** an LSP server reusing the compiler as a library
  (`Lsp.hs`), publishing determinacy diagnostics with hovers/lenses surfacing
  the determinacy proof.
- **L (profiler):** per-source-line constraint-cost attribution via the
  lowering's `origin` strings (`Profile.hs`); sums reconcile with `zkc-stats`.
- **M (gadget stdlib):** a `std/` of gadgets written in `.zkc`, each proved
  determinate by the same analysis, each with a negative fixture, plus a `use`
  include mechanism (`Reference.hs`, `std/REFERENCE.md`, `zkc doc`).

### Phase 7 — done (`docs/phase7.md`)
- **N (formal verification of the lowering):** N.1 an executable IR spec
  (`Ir::is_satisfied` / `unmet` in `backend/zkc-core/src/ir.rs`); N.2 per-rule
  faithfulness, exhaustively over F₁₃ (`lowering_faithfulness_tests.rs`); N.3 a
  mutation harness (each lowering mutation is caught).
- **O (recursion):** O.1 a FRI-fold verifier written *in the language*
  (`std/fri_fold.zkc`, `std/rlc.zkc`, `examples/fri_verify.zkc`); O.2 a real
  fold verified inside an outer proof (`recursion_tests.rs`).
- **The full in-circuit FRI verifier** — Merkle-path openings + fold + final
  check, verifying a real FRI query *inside* an outer STARK
  (`std/hash_leaf.zkc`, `std/compress.zkc`, `examples/fri_verify_full.zkc`,
  `fri_verifier_tests.rs`).
- **In-circuit Fiat–Shamir** — the fold challenge derived from the commitment
  in-circuit, bit-exact with the backend transcript (`std/fs_challenge.zkc`,
  `examples/fri_verify_fs.zkc`).
- **The query index made algebraic** — `transcript.challenge_index` now
  computes `challenge mod domain` (the canonical low bits) instead of folding
  decimal digits, so the index is a genuine reduction of the challenge
  (`index_binding_tests.rs`).
- **The `bits` decomposition hint** — a new language primitive (see §3 and
  `docs/bits-hint.md`), which unlocked general range checks (`std/range8.zkc`)
  that the language could not previously express.
- **The sound query index — the finding closed.** `std/canonical_low2.zkc`
  reads the index off a pinned 64-bit decomposition instead of relating it to
  the challenge, and refuses the non-canonical decompositions Goldilocks admits.
  Proved by enumeration over the prover's entire freedom
  (`index_binding_tests.rs`), determinate with no case split and no SMT.
- **A verifier that trusts nothing about its query** —
  `examples/fri_verify_idx.zkc` derives the query position from the transcript
  and binds the Merkle path bits and the evaluation point to it. The test that
  matters hands it a *genuine* opening of the *genuine* root at a position the
  transcript did not choose — an attack every earlier verifier here accepted —
  and shows the path assertions passing while the position binding refuses it.

### Real hash (a resolved phase-5 boundary)
A real **Poseidon** over Goldilocks now exists (`backend/zkc-core/src/poseidon.rs`)
behind the `Hasher` trait, exercised end-to-end through the STARK
(`stark_poseidon_tests.rs`). The earlier `ToyHash` (`x^7`) is retained only for
small in-circuit verifier tests where a trivially-expressible hash keeps the
example circuits legible.

---

## 3. Key decisions (recent additions)

Earlier decisions (uniqueness-as-self-composition; SMT soundness asymmetry;
Plonkish over trace-AIR; free variables are atoms; gate constraint alone catches
the forgery) still stand. New with phase 7:

- **The in-circuit index binding is determinate but *unsound* — a finding, not a
  feature.** *(Since closed — see the two entries after this one; the finding is
  kept because it is the reason the rest exists.)* The natural binding `challenge == index + domain*high` (index bits
  constrained) *proves determinate* — `idx` is a function of the inputs — yet is
  forgeable: `high` is free, so the prover hits any index via
  `high = (challenge - index)/domain`. The lesson: **determinacy rules out
  under-constrained outputs; it does not certify that an output equals a
  canonical reduction** (a range property). Demonstrated with proof in
  `index_binding_tests.rs` and `examples/index_from_challenge.zkc`; written up in
  `docs/in-circuit-index.md`. This is what motivated the `bits` hint.
- **`bits` desugars in the parser, not the elaborator.** `advice (b0,..,bk) =
  bits(x);` expands to single-bit advice + a `b_i*(1-b_i)==0` constraint each +
  the reconstruction `x == Σ b_i*2^i`. No new elaborator machinery; the
  reconstruction is the load-bearing part (it both pins the bits and range-limits
  `x` to `[0, 2^(k+1))`).
- **`bits` determinacy is a marking, not a search (`closeBits`).** A bit
  decomposition is exactly the case the decidable core could not settle (one
  equation, many unknowns) and that older phases left to SMT. The `closeBits`
  rule instead certifies it directly: *once a bits node's source is determined,
  so are its bits*, sound because binary decomposition is injective on
  `[0, 2^n)`. Being a marking (not a case-split), it costs nothing and **scales**
  — 32- and 62-bit decompositions prove as readily as 2-bit — which is what makes
  `bits`-based range checks practical without SMT. (Limitation: the pre-pass
  marks bits from sources determined *before* the search; a source determined
  only mid-search is a false negative, never unsound.)
- **The sound index reads the position off, rather than relating it to the
  challenge.** Given `bits`, the natural fix — range-check `high` in
  `challenge == index + domain*high` — is not the one to make. Decomposing the
  challenge into all 64 bits and taking the index from the bottom of the
  decomposition is simpler *and* strictly stronger: the reconstruction leaves no
  freedom at all, and the range bound on the upper bits comes for free because
  they are themselves a `bits` decomposition. Determinacy proves it as a
  marking, with no case split and no SMT.
- **Canonicity is one constraint, and it is load-bearing.** Goldilocks wraps at
  `p = 2^64 - 2^32 + 1`, *below* `2^64`, so a 64-bit string is not a unique
  representative: for any canonical `c < 2^32 - 1` the string for `c + p` also
  reconstructs, with different low bits. The non-canonical strings are exactly
  those with all top 32 bits set and a nonzero low half, so
  `(all top bits set) * (low 32 bits) == 0` refuses all of them and no canonical
  one. The test proves it is load-bearing rather than defensive: on the sharpest
  wrap case every other obligation is met and this assertion alone refuses the
  witness. The all-ones test is a 31-multiplication product rather than an
  `is_zero`, which keeps the gadget free of advice and case splits.
- **DEEP moves the constraint check off the domain, and that is the point.**
  The old STARK checked `composite = Q·Z_H` pointwise at the queried positions.
  That is a spot check of the committed columns, and the positions are a public
  function of the commitment, so a prover can grind until they miss a corrupted
  one. Checking the identity *once, at an out-of-domain `ζ`* drawn after every
  commitment, and binding the claimed values back with the quotients
  `(P(x) - P(ζ))/(x - ζ)` batched into FRI, replaces the spot check with a test
  that every position is subject to. Measured cost: **seven field elements**
  (one commitment, six out-of-domain values). The per-query openings did not
  grow — the rotated `Z` opening is gone, and the quotient opening takes its
  place.
- **Degree correction is what makes a batch mean anything.** Each DEEP quotient
  enters the batch scaled by `λ + λ'·x^e`, not a plain `λ`. Without it the batch
  is bounded by the largest degree in it, and a trace column of a third that
  degree would pass a test it should fail. The exponent per quotient is chosen
  so the padded term lands just inside the FRI bound.
- **One implementation of the batch, called by both sides.** `deep_batch` is
  shared by prover and verifier. Two agreeing implementations of a random linear
  combination is exactly the duplication that rots into a soundness bug nobody
  can see, because each side stays self-consistent while both drift from the
  protocol. Same reasoning for `draw_ood_point`.
- **The hint IR is a string + optional bit index, not an enum.** The backend
  hint node carries `hint: String` + `bit: Option<u32>` (was a `HintKind` enum),
  so new hint kinds are additive and backward-compatible; the witness solver
  reads bit `i` of the argument's canonical representative.

---

## 4. Open issues and explicit boundaries

Deliberately unfinished, scoped-out work — not bugs.

- **SMT — no longer a boundary; the path is exercised.** Earlier checkpoints
  recorded that no solver was installable and the phase-3B escalation could not
  be run. That is now false: `apt-get install z3` (Ubuntu universe, z3 4.8.12)
  works, and the escalation runs end to end in the `int` dialect —

      zkc build f.zkc -o /dev/null --smt-solver z3 --smt-dialect int --smt-timeout 20

  On a deliberately under-constrained gadget (`assert out * out == x`) the
  decidable core stalls, z3 refutes, and the compiler reports the forgery it
  built: `x = 4`, `out = 2` vs `out = -2`. So the refutation path — the half of
  the SMT work that had never been observed working — is confirmed. The default
  solver is still cvc5 (`QF_FF`), which is *not* packaged for Ubuntu; z3 needs
  `--smt-dialect int` because it has no finite-field theory. Everything in the
  stdlib and all phase-7 work continues to prove via the decidable core.
- **Toolchain — `Cargo.lock` needs local downgrades; never commit them.** See §6.

---

## 5. Next steps

**No core soundness boundary is open.** The roadmap was complete before; with
DEEP the two boundaries §4 used to carry are closed as well. What is left is
polish, and none of it is load-bearing:

1. **The write-up.** Blog post, GitHub Pages, the longer treatment. The project
   is at the point where the artifacts — the determinacy finding, the
   determinate-but-unsound index binding, the spot-check-versus-proof of DEEP —
   are what the writing would be about.

---

## 6. How to build and test (environment notes)

**Frontend (Haskell).** The compiler depends only on GHC boot libraries (base,
containers, mtl) — there is no package manager in the loop, so *any* modern GHC
works; the build just uses the active `ghc`.
```
make -C compiler all                       # → compiler/build/zkc
# tests:
cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs -o build/spec tests/Spec.hs && ./build/spec
```

**IDE / HLS.** Because this is a bare-`ghc` project (no cabal/stack), HLS needs
a cradle: `compiler/hie.yaml` (a `direct` cradle passing `-isrc -itests`) is
**committed** — that is what lets HLS resolve the `Zkc.*` modules. Two toolchain
lessons worth keeping (learned the hard way):
- HLS ships one binary *per exact GHC point release*. Do **not** chase the newest
  GHC; pick one whose HLS binary reliably exists — **9.8.4** or **9.6.7** are
  safe (full support, stable Windows bindists). The wrapper falls back to a
  mismatched binary otherwise and reports "HLS does not support GHC x.y.z yet".
- Keep HLS current via `ghcup` (`ghcup install hls latest && ghcup set hls
  latest`), and set the VS Code Haskell extension's *Manage HLS* to `GHCup`. The
  extension may still prompt to download the HLS build matching the active GHC —
  let it.

**Backend (Rust).** The toolchain is pinned in `rust-toolchain.toml` to
**1.97.1**; with `rustup` installed, that is what you get and nothing else is
needed.
```
cd backend && cargo test                   # all tests (135)
cargo build --bin zkc-stats                # arithmetization cost accounting
cargo build --bin zkc-profile              # per-source-line cost attribution
cargo build --bin zkc-check                # lower + self-check, --arith r1cs|plonkish
```

**The old "recurring toolchain fix", explained and mostly gone.** Earlier
checkpoints carried four `cargo update --precise` lines as a fix to reapply
every session. They were never a defect in the repo — they are what an *older*
cargo than the pinned one needs. Specifically, a distro cargo (Ubuntu 24.04
ships 1.75.0, which is what a container without `rustup` gets) cannot parse
`zeroize_derive 1.5.0`, because that crate is edition 2024 and 1.75 predates it.
Retiring `zkc-prove` removed the arkworks Groth16 chain and with it the two
`rayon` pins entirely. What is left, and only on an old cargo:
```
cargo update -p zeroize --precise 1.8.1
cargo update -p zeroize_derive --precise 1.4.2
```
Local only — do **not** commit them; the committed lock is correct for the
pinned toolchain. `ark-ff`/`ark-bn254` remain (they are how the project
instantiates BN254, which is half the "generic over the field" invariant), which
is why `zeroize` is still in the tree at all.

**IR fixtures.** Four backend tests compile in real frontend output. The files
live in `backend/zkc-core/tests/fixtures/` and are **committed**, so `cargo test`
needs no GHC and no absolute paths; `scripts/fixtures.sh --check` proves they are
still byte-for-byte what the frontend emits (the emitter is deterministic, so the
check is a plain `cmp`), and `scripts/fixtures.sh` regenerates them. Run the
check after touching the frontend or any of the four `.zkc` sources. Hand-written
IR — the per-rule specs in `lowering_faithfulness_tests`, the negative fixtures in
`core_tests` — is deliberately *not* under the script: no source compiles to it.

**SMT:** z3 is installable (`apt-get install z3`) and the escalation path runs —
see §4 for the invocation and the confirmed refutation. cvc5, the default and the
only one with native `QF_FF`, is still not packaged.

---

## 7. Repository map

```
compiler/                        Haskell frontend (boot libraries only)
  hie.yaml                       HLS cradle: direct, -isrc -itests
  Makefile                       bare ghc; SRC=src, BUILD=build
  src/Main.hs                    CLI: build, doc, lsp; --explain, --no-smt,
                                 --smt-*, --dump-smt
  src/Zkc/
    Syntax/{Lexer,Parser,Ast}.hs Parser desugars bits(); AST carries HintBit
    Analysis/{Determinacy,Smt}.hs the type system (+ closeBits) and SMT escalation
    Core/{Ir,Elaborate}.hs       elaboration; HintKind = KInvOrZero|KInv|KBits i
    Emit/Json.hs                 IR emission (hint + bit index)
    Diagnose.hs, Json.hs         structured + JSON diagnostics (phase 6 J)
    Lsp.hs, Profile.hs           language server (K), cost profiler (L)
    Reference.hs, Field.hs, Diagnostics.hs
  tests/Spec.hs                  158 frontend checks
examples/*.zkc                   iszero, divide, mul_square, relation,
                                 fri_verify{,_full,_fs,_idx},
                                 index_from_challenge{,_sound,16}, ...
                                 (repo root, not under compiler/)
scripts/
  run_all.sh                     end-to-end demo; checks generated artefacts first
  fixtures.sh                    regenerate / --check the IR test fixtures
  gen_canonical.sh               regenerate / --check the canonical_low family
std/                             gadget stdlib (each .zkc proved determinate)
  is_zero, inverse, assert_bit, assert_range4, mux,           (phase 6 M)
  fri_fold, rlc, hash_leaf, compress, fs_challenge,           (phase 7 O)
  range8                                                       (phase 7, bits)
  fs_index_challenge                          (phase 7, the sound query index)
  canonical_low{1,2,3,4}         GENERATED by scripts/gen_canonical.sh
  reference.zkc                  doc driver: uses all 16 gadgets in one scope
  tests/*_broken.zkc             a negative fixture per gadget
  REFERENCE.md                   generated by `zkc doc`, byte-checked by the
                                 frontend suite
backend/
  zkc-core/                      crypto-free; generic over ZkField
    src/ir.rs                    neutral Core IR + executable spec (is_satisfied)
    src/field.rs, goldilocks.rs  ZkField/TwoAdicField; hand-written Goldilocks
    src/lower.rs, r1cs.rs, plonkish.rs   two lowerings + fusion + validate
    src/witness.rs               witness solver (inv, inv_or_zero, bits)
    src/fft.rs, hash.rs, poseidon.rs, merkle.rs, transcript.rs
    src/air.rs, fri.rs, stark.rs the STARK (gate constraint + permutation,
                                 DEEP out-of-domain check + batched FRI)
    tests/                       core, goldilocks, fft, commitment, fri, stark,
                                 poseidon, stark_poseidon, lowering_faithfulness,
                                 recursion, fri_verifier, index_binding, bits,
                                 deep
    tests/fixtures/*.ir.json     committed frontend output (see §6)
  zkc-tools/                     CLI tooling over the neutral IR: zkc-stats,
                                 zkc-profile, zkc-check. No proving system —
                                 the borrowed arkworks Groth16 backend that
                                 used to live here is retired.
README.md                        the project README (root); the phase-7 plan
                                 that used to sit there is docs/README_phase7_plan.md
docs/
  ROADMAP.md, DESIGN_DECISIONS.md, README_phase0..7.md
  phase5-status.md, phase6.md
  APPLY.md                       change note for the most recent drop
  bits-hint.md                   the decomposition-hint primitive
  in-circuit-index.md            the determinate-but-unsound finding, and how
                                 it was closed
  benchmarks.md, CHECKPOINT.md   (this file)
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
tiny-circuit timings favour the STARK; its proof size is inflated by the opening
format.)
