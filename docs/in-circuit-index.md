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

## The missing primitive

Soundness needs `high` range-checked, which needs the challenge fully
decomposed into bits — and the language has no way to introduce those bits. Its
only advice is `inv` / `inv_or_zero`; `assert_range4` already notes in passing
that "a general 2^n range needs bit decomposition, which needs a decomposition
hint the language does not yet provide."

So the next primitive is a **decomposition hint** — an advice form
`bits(x, n)` that supplies the `n` low bits of `x`, alongside the constraints
that each is a bit and that they reconstruct `x`. With it, `high` (and the
index) can be range-checked, and the in-circuit index derivation becomes sound.

One caveat carries over from phase 3: the determinacy of a bit decomposition is
not settled by the decidable core — it is one of the cases (with `is_equal`)
that needs the SMT-backed checker. So the decomposition hint and the SMT escape
hatch are the two pieces that, together, would let the verifier derive its query
index in-circuit and be both determinate and sound. Until then, the index stays
an input, and this note marks the reason.
