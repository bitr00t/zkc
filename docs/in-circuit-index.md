# In-circuit query-index derivation — status and the missing primitive

In-circuit Fiat-Shamir made the FRI verifier derive its *fold challenge* from the
commitment (see `std/fs_challenge.zkc`). The other Fiat-Shamir value is the
*query index* — which positions of the codeword are opened. Deriving it
in-circuit turns out to sit exactly on the boundary of what the determinacy type
system can guarantee, and this note records where that boundary is and what is
needed to cross it.

## What was done

The backend now derives the index as an honest algebraic reduction. Previously
`challenge_index` folded the *decimal digits* of the challenge — a deterministic
but non-algebraic function. It now computes `challenge mod domain`: the low bits
of the challenge's canonical representative, the value an in-circuit derivation
would have to reproduce. FRI prove and verify move in lockstep as before, so this
is behaviour-preserving for the round trip; the point is that the index is now a
*reduction of the challenge*, not a hash of its digits.

## Why the in-circuit derivation is not yet sound

The natural in-circuit binding is: the prover supplies the index bits and a
quotient `high`, and the circuit checks

    challenge == index + domain * high

with each index bit constrained to `{0,1}`. This **proves determinate** — `idx`
is a function of the inputs — and it is tempting to stop there.

It is unsound. `high` is unconstrained, so for *any* index in `[0, domain)` the
prover can pick `high = (challenge - index) / domain` and satisfy every
constraint. The index is not bound to the challenge at all. Both facts are
demonstrated concretely:

- Frontend: `examples/index_from_challenge.zkc` is proved determinate
  (`indexBindingCase` in the test suite passes).
- Backend: `naive_index_binding_is_determinate_but_unsound` shows that *every*
  index in `{0,1,2,3}` satisfies the circuit.

The lesson is precise: **determinacy rules out under-constrained outputs; it does
not certify that an output equals a canonical reduction.** "The index is the low
bits of the challenge" is a *range* property (it requires `high` to be the true
quotient, i.e. `high < p / domain`), and range properties are exactly what a
purely determinacy-based check does not see.

## The missing primitive — now provided

Soundness needs `high` range-checked, which needs the challenge decomposed into
bits — and until phase 7 the language had no way to introduce those bits. It now
does: the **`bits` decomposition hint** (see `docs/bits-hint.md`). Writing

    advice (h0, h1, .., h61) = bits(high);

supplies `high`'s bits and emits the constraints that pin them, forcing
`high` into `[0, 2^62)` — a genuine range check, which the `closeBits`
determinacy rule proves determinate without SMT even at that width. So the
range check the index binding needs is now expressible and provable.

One subtlety remains before the in-circuit index is *fully* sound over the
field. Range-checking `high` to `[0, 2^62)` and `index` to `[0, 4)` bounds
`index + 4*high` to `[0, 2^64)`, but the field wraps at `p ≈ 2^64 - 2^32`, so a
second decomposition of `challenge + p` can exist for small challenges. Ruling
it out needs the canonical check `challenge < p` — itself a `bits`-based
comparison against the modulus. That is now writable too; wiring the whole
sound derivation into the verifier is the remaining step, and it no longer waits
on a missing primitive.
