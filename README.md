# Phase 5 — own prover: FRI over Goldilocks

> Design note. Decisions are marked and overridable; the one measurement that
> shapes the whole phase is at the top, because it was worth checking before
> committing to any of this.

## The measurement that comes first

Phases 1–4 borrow a prover: lowered R1CS goes to arkworks' Groth16 over BN254.
Phase 5 replaces that with a hand-written FRI/STARK prover — and a STARK wants
the *opposite* field from a pairing-based SNARK. Groth16 needs a ~254-bit
pairing-friendly field; FRI needs a *small* field with high two-adicity, so
that the FFTs it is built on are cheap. Goldilocks, `p = 2^64 - 2^32 + 1`, is
the canonical choice: it fits in a machine word, and `p - 1` is divisible by
`2^32`, giving FFT domains up to a billion rows.

The entire backend is generic over `ZkField` rather than tied to BN254 — an
invariant maintained since phase 1 precisely for this moment. Before designing
anything, that invariant was tested the way phase 4 tested IR neutrality:
instantiate the existing lowerings over Goldilocks instead of BN254 and see
whether anything breaks.

Nothing does. `lower::<Goldilocks>` and `lower_plonkish::<Goldilocks>` compile
and produce **identical constraint counts** to BN254 (IsZero: 2 and 2), and the
field arithmetic checks out (`3 * 5 = 15` in the small field). So the frontend,
the elaborator, the determinacy pass, both lowerings, the witness solver and
the two checkers are all already field-agnostic in fact, not just in principle.
Phase 5 does not touch any of them. It adds a field and a prover beneath them.

That is the shape of the whole phase, and it is worth stating plainly: **the
new work is a leaf**, hung under an interface everything else already speaks.

## What a STARK actually requires

A FRI-based STARK proves that a committed set of polynomials satisfies a set of
constraints, using no trusted setup and only a hash function for its
cryptography. The pieces, and which we already have:

* **A small field with high two-adicity.** *New.* A hand-written Goldilocks —
  the reason the phase exists.
* **An arithmetization as polynomials over an evaluation domain.** *Have it,
  mostly.* Phase 4's Plonkish is exactly a table of rows with a gate identity
  and a permutation (copy) argument — the STARK-friendly shape. This is why
  phase 4 chose Plonkish over R1CS: a STARK proves the Plonkish circuit almost
  directly, whereas R1CS would need re-expressing.
* **Low-degree extension and FFT.** *New.* Interpolate each column over a coset,
  evaluate on a larger domain.
* **A commitment: Merkle trees over a hash.** *New.* Commit to the column
  evaluations; FRI queries open a few leaves.
* **FRI itself.** *New.* The low-degree test that makes the whole thing a
  succinct argument.
* **Fiat–Shamir.** *New.* A transcript that turns the interactive protocol
  non-interactive by deriving the verifier's challenges from a hash of
  everything committed so far.

Only the field and the STARK machinery are new. The circuit reaching the prover
is the Plonkish one phase 4 already builds, validates, and self-checks.

## Decision: build the field, borrow the hash, build FRI

Three sub-choices, each marked.

**The field is hand-written.** This is the point of the phase and the one place
"borrow it" would defeat the purpose — the whole roadmap is *own* language,
*own* arithmetization, *own* prover. Goldilocks arithmetic is also genuinely
small: addition, multiplication with the special-form reduction that makes this
prime fast, inversion, and the two-adic roots of unity FFT needs. It implements
the existing `ZkField` trait plus a `TwoAdicField` extension for the roots, and
everything upstream keeps working by construction.

**The hash is borrowed, at first.** A STARK's security rests on its hash, and a
hand-rolled hash is exactly the kind of thing that should not be trusted
without cryptographic review. The prover is written against a `Hasher` trait
and instantiated with a vetted arithmetic-friendly hash (Poseidon or
Rescue-Prime over Goldilocks) from a reviewed crate. Swapping in a hand-written
one later is a leaf change, the same way this whole phase is. *Overridable:* if
the goal is zero dependencies over speed, the hash can be hand-written too, at
the cost of taking on its analysis.

**FRI is hand-written.** It is the intellectual core of the phase and the thing
worth understanding end to end; borrowing it would hollow the exercise out.

## Workstreams

### G — Goldilocks

**G.1 — The field.** *Done.* `goldilocks.rs`: a `ZkField` impl over a reduced
`u64`, with the special-form reduction that makes this prime fast (`2^64 ≡
2^32 - 1`, so a 128-bit product folds with a few word ops and no division),
Fermat inversion, and `pow`. It is differentially tested against an
independent arkworks Goldilocks on 50,000+ random inputs per operation, biased
toward the hard cases near 0 and near `p`, plus the worst products near
`(p-1)²` where a reduction bug would hide. The reference is test-only. The
existing R1CS and Plonkish lowerings, instantiated over this hand-written
field, produce identical counts to BN254 — the leaf really is a leaf.

**G.2 — Two-adicity and FFT.** *Done.* A `TwoAdicField` extension trait
(`TWO_ADICITY = 32`, `two_adic_generator`) and `fft.rs`: iterative
Cooley–Tukey `ntt`/`intt` and a `coset_lde`, all generic over `TwoAdicField`
so nothing names Goldilocks. Pinned by the properties that define an FFT: the
generators have exactly the claimed order (`g^(2^(k-1)) = -1`), inverse-undoes-
forward round-trips to `n = 2^12`, the forward transform agrees with Horner
evaluation point by point, and the LDE's extended evaluations match evaluating
the same polynomial at the coset points — a redundant encoding, not a
different function.

### H — Commitment and transcript

**H.1 — Merkle commitment.** *Done.* `merkle.rs`: a `MerkleTree` over the
`Hasher` trait, padding to a power of two so paths are uniform, with `open` and
a standalone `verify_opening` a root-only verifier can run. The security is all
in the opening, so the tests are: every honest opening verifies, and a tampered
one is rejected three ways — a forged leaf, a corrupted sibling, and a leaf
claimed at the wrong index. A changed leaf changes the root, so the root binds
the whole vector.

**H.2 — Fiat–Shamir transcript.** *Done.* `transcript.rs`: a `Transcript` over
the `Hasher`, domain-separated at construction, with `absorb`/`absorb_digest`
and `challenge`/`challenges`/`challenge_index`. A counter is mixed into each
squeeze so successive challenges from one commitment differ (FRI needs several
query positions). Tested on the property soundness rests on: replaying the same
messages yields the same challenges, and changing *any* absorbed message — its
value, its order, or the domain separator — changes every subsequent challenge.

Both are written against a `Hasher` trait (`hash.rs`) and tested through a
transparent stand-in permutation (`x^7` sbox) that carries no security claim of
its own; the reviewed arithmetic hash is the leaf swap the plan defers. Nothing
in the tree or the transcript names a concrete hash.

### I — The STARK

**I.1 — Plonkish to AIR-style constraints.** *Done.* `air.rs`: the Plonkish
table becomes polynomials. Interpolating the three witness columns and five
selectors over a size-`n` domain turns the per-row gate identity into a single
polynomial `C(x) = q_L·a + q_R·b + q_O·c + q_M·a·b + q_C`, and "the gate holds
on every row" becomes "`C` vanishes on the domain", i.e. `C` is divisible by
`Z_H(x) = x^n - 1`. Verified directly: on an honest witness the quotient
`Q = C/Z_H` has no high-degree coefficients and `Q·Z_H = C` at a random point.
The copy constraints are built into the AIR as a permutation `σ` over cell
positions (union-find over the equality classes), and — as of the wiring
hardening — enforced in the proof by a grand-product permutation argument
(see I.2).

**I.2 — FRI prover and verifier.** *Done.* `fri.rs` is the low-degree test —
Cooley–Tukey folding with a verifier challenge each round, Merkle commitment
per layer, and a query phase that checks the fold chain and openings; tested so
that an honest low-degree polynomial passes and a high-degree one is rejected.
`stark.rs` composes it: commit the trace, form `Q = C/Z_H`, FRI-prove `Q` is
low-degree, and check `C = Q·Z_H` at the queried points against the opened
trace and verifier-computed selectors, all bound by a Fiat–Shamir transcript.
The end-to-end tests are the phase's payoff and use no arkworks: **an honest
witness proves and verifies, and the phase-0 forgery yields no accepted proof**
— caught because the forgery is a gate violation, so `Q` is not a polynomial
and the consistency check fails. A property test also found and fixed a real
verifier weakness (a proof must carry exactly the configured number of FRI
queries, not fewer).

*Wiring hardening (done):* the STARK now also enforces the **wiring**, via a
PLONK-style grand-product permutation argument over `σ`. A grand-product column
`Z` is committed alongside the trace; two constraints (`Z` starts at 1, and the
recursion `Z(ωx)·g - Z(x)·f = 0`) force every `σ`-cycle to hold a single value.
A dedicated test builds a circuit whose gates are trivially satisfied (all
selectors zero) but whose two cells are wired together, and checks that a trace
putting different values in them is **rejected** — the case the gate constraint
alone would accept.

*The one boundary left explicit:* binding the committed trace and `Z` columns
to low degree via a FRI batch (DEEP). FRI here proves the composite quotient is
low-degree; the trace and `Z` are committed and opened for the consistency
check but not themselves folded into the low-degree test. This is the standard
next hardening; it does not affect the honest, forgery, or wiring results, and
is marked plainly in the tradition of this project's honest partials
(Workstream C.2, the cvc5 finite-field limitation).

**Order: G → H → I.** Each needs the last. G is testable in complete isolation
(a field is a field); H needs G's FFT for nothing but is cleaner built on the
tested field; I needs both.

## What it costs, and how we will know

Phase 4's `zkc-stats` already reports Plonkish rows, which is the STARK's trace
length — so the cost model is in place before the prover is. Phase 5 adds the
numbers a STARK is actually judged on: proof size, prover time, verifier time,
each as a function of trace length. The comparison against the Groth16 baseline
is the honest one — Groth16 proofs are tiny and verification is constant-time,
while a STARK trades larger proofs for no trusted setup and a hash-only trust
assumption. The point is not that one wins but that the compiler can now put
both on the table, the same way phase 4 put two arithmetizations on the table.

## Scope, drawn on purpose

- **No recursion.** Proofs about proofs are phase 7. Phase 5 proves circuits.
- **The hash is a dependency, deliberately.** See the decision above; a
  hand-written hash without review would be the least trustworthy line in the
  system.
- **The reference field is a test-only dependency.** Goldilocks-from-arkworks
  exists in phase 5 solely as the oracle the hand-written field is
  differentially tested against, exactly as `ark-bn254` is a dev-dependency
  today. It is never in a shipped path.
- **Performance is correctness-first.** The FFT and FRI are written to be
  obviously right before they are written to be fast; the roadmap's profiler
  (phase 6) is where speed gets systematic attention.
- **The frontend does not change — again.** The measurement at the top is the
  evidence it will not have to. If it does, that is a finding, not a patch.

## What "done" looks like

1. A hand-written Goldilocks field passing a differential test against the
   reference, implementing `ZkField` so the rest of the compiler is unchanged.
2. An FFT/LDE whose round-trip and known-answer properties hold.
3. A Merkle commitment and a Fiat–Shamir transcript, each with a tamper test.
4. A FRI prover and verifier: the honest witness proves and verifies; the
   phase-0 forgery does not.
5. arkworks removed from the proving path, present only as a test oracle.
6. Proof-size and timing numbers alongside the Groth16 baseline.
7. **Not one line of the frontend changed.**
