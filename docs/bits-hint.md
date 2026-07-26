# The `bits` decomposition hint

`bits` is the language's third advice form, after `inv` and `inv_or_zero`. It
decomposes a value into its low bits, and it is the primitive the standard
library had been flagging as missing — `assert_range4` noted that a general
`2^n` range check "needs a decomposition hint the language does not yet
provide." Now it does.

## Syntax

    advice (b0, b1, .., bk) = bits(x);

Inside a gadget, this binds `k+1` names to the low bits of `x` (least
significant first). Like any advice, the bits are prover-supplied; unlike a lone
`advice`, this form *also* emits the constraints that pin them, so the bits are
not free.

## What it desugars to

The parser expands the form into primitives — no new elaborator machinery:

- one single-bit advice per name, `advice b_i = <bit i of x>`;
- a bit constraint `b_i * (1 - b_i) == 0` for each, forcing `b_i ∈ {0,1}`;
- a reconstruction `x == b0 + 2*b1 + .. + 2^k*bk`.

The reconstruction is the load-bearing part. Because each `b_i` is a bit, its
right-hand side lies in `[0, 2^(k+1))`, so the equation both pins the bits to
`x` and forces `x` into that range. A range check falls straight out: decompose
`x` into `n` bits and the constraint system is satisfiable exactly when
`x ∈ [0, 2^n)`. That is `std/range8.zkc`.

## Why it is determinate without SMT

A bit decomposition is exactly the case earlier phases could not settle with the
decidable core: the reconstruction is one equation in many unknowns, so neither
linear solving nor case splitting pins the bits, and it was left for the
SMT-backed checker. `bits` sidesteps that with a dedicated determinacy rule,
`closeBits`: **once a bits node's source is determined, so are its bits.**

The rule is sound because binary decomposition is injective on `[0, 2^n)` — the
emitted constraints admit exactly one bit pattern for each value of the source,
so the bits are a function of it. The rule is a marking, not a search, so it
costs nothing and scales: a 32-bit (or 62-bit) decomposition proves determinate
as readily as a 2-bit one, which is what makes `bits`-based range checks
practical. It runs as a fixpoint, so a decomposition whose source is itself
built from other bits resolves in turn.

The one limitation is deliberate: the pre-pass marks bits determined from
sources determined *before* the case-split search. A source that only becomes
determined mid-search is not picked up — a false negative, never unsoundness,
and not a case that arises for the range checks this was built for.

## Backend

A bits hint carries its bit index (`"hint": "bits", "bit": i`). The witness
solver reads bit `i` of the argument's canonical representative. The rest of the
pipeline treats it like any other hint — an atom the constraints pin down.

## What it unlocks

- General `2^n` range checks (`std/range8.zkc`), replacing the membership-product
  trick that only scaled to tiny sets.
- The range check the in-circuit query index needs (see
  `docs/in-circuit-index.md`).
- Comparisons and canonical-form checks, which reduce to range checks.
