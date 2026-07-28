# In-circuit query-index derivation — the finding, and how it was closed

In-circuit Fiat-Shamir made the FRI verifier derive its *fold challenge* from the
commitment (see `std/fs_challenge.zkc`). The other Fiat-Shamir value is the
*query index* — which positions of the codeword are opened. Deriving it
in-circuit turned out to sit exactly on the boundary of what the determinacy type
system can guarantee.

This note is kept in the order things happened, because the order is the
argument: what the backend derives, why the obvious in-circuit binding is
determinate *and* forgeable, what primitive was missing, and what the sound
derivation finally looks like. **Status: closed.** The sound derivation is
`std/canonical_low2.zkc`, it is proved by enumeration in
`backend/zkc-core/tests/index_binding_tests.rs`, and it is wired into a verifier
that now trusts nothing about its query (`examples/fri_verify_idx.zkc`).

## What was done

The backend now derives the index as an honest algebraic reduction. Previously
`challenge_index` folded the *decimal digits* of the challenge — a deterministic
but non-algebraic function. It now computes `challenge mod domain`: the low bits
of the challenge's canonical representative, the value an in-circuit derivation
would have to reproduce. FRI prove and verify move in lockstep as before, so this
is behaviour-preserving for the round trip; the point is that the index is now a
*reduction of the challenge*, not a hash of its digits.

## Why the obvious in-circuit derivation is not sound

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

## The missing primitive — provided, then used

Soundness needs `high` range-checked, which needs the challenge decomposed into
bits — and until phase 7 the language had no way to introduce those bits. It now
does: the **`bits` decomposition hint** (see `docs/bits-hint.md`). That is what
unblocked the rest of this note.

## How the loop was closed

The final gadget does not range-check `high` at all. Once the bits exist, the
cleaner move is to stop *relating* the index to the challenge and start *reading
it off*: decompose the challenge into all 64 of its bits, and take the index
from the bottom of that decomposition. The reconstruction the desugaring emits,

    challenge == b0 + 2*b1 + 4*b2 + ... + 2^63*b63

leaves the prover no freedom — the bits *are* the representative — and the
range check on `high` comes for free, because the upper 62 bits are a `bits`
decomposition and so are bounded by construction. `std/canonical_low2.zkc` is
that gadget; it returns `i0` and `i1`, from which a domain of size 2 takes the
index `i0` and a domain of size 4 takes `i0 + 2*i1`.

The `closeBits` rule proves the whole thing determinate with **no case split and
no SMT**: a 64-bit decomposition costs a marking, not a search. That is the
practical reason this shape was reachable at all.

## The wraparound, and why it is not a footnote

One subtlety is specific to Goldilocks and is the reason the gadget is a hundred
lines rather than three. The field wraps at `p = 2^64 - 2^32 + 1`, which is
*below* `2^64`, so a 64-bit string is **not** a unique representative. Whenever
the canonical value `c` is smaller than `2^64 - p = 2^32 - 1`, the string for
`c + p` is also 64 bits wide and also satisfies the reconstruction — and its low
bits differ from `c`'s. A prover holding that second string moves the query
index. It happens for about one challenge in `2^32`, which is rare, and rare is
not sound.

The non-canonical strings are exactly those in `[p, 2^64)`, and because of the
shape of `p` that interval has an exact description: **the top 32 bits are all
set, and the low 32 bits are not all zero.** So one constraint suffices:

    (all top bits set) * (low 32 bits) == 0

It refuses every non-canonical string and no canonical one — including `p - 1`,
whose top bits are all set and whose low half is zero. The all-ones test is a
product of the 32 top bits: 31 multiplications, no advice, no case split.

## What is now proved

In `backend/zkc-core/tests/index_binding_tests.rs`, by enumeration rather than
by assertion. The prover's entire freedom is the choice of bit string, and there
are at most two strings congruent to any challenge (`c` and `c + p`; `c + 2p`
never fits 64 bits), so the tests walk *all* of them against *all* four claimed
indices:

- `the_sound_binding_accepts_exactly_the_honest_index` — for an ordinary
  challenge, a small one, `2^32 - 2` (the largest challenge that wraps), `p - 1`
  and `0`, exactly one witness survives, and its index is the challenge's low
  bits.
- `the_forged_index_that_satisfies_the_naive_binding_is_now_refused` — the same
  forgery, refused.
- `the_canonicity_check_is_the_load_bearing_constraint` — the sharpest wrap
  case, `c = 2^32 - 2`, whose alternative string is the all-ones `2^64 - 1`.
  Every bit is a bit, the reconstruction holds, the claimed index matches the
  supplied bits: **exactly one** obligation refuses the witness, and the test
  names it. Drop that assertion and the circuit accepts two indices.

The naive test is kept alongside, still passing, still showing all four indices
satisfying the old binding. The contrast is the point.

## Wired into the verifier

`examples/fri_verify_idx.zkc` is the in-circuit FRI verifier with nothing left
on trust. The fold challenge was already derived (`fri_verify_fs.zkc`); now the
query position is too, from the transcript state after the final codeword is
absorbed (`std/fs_index_challenge.zkc`), and everything the position touches is
bound to it — the Merkle path bits of both openings, and the evaluation point
`x`, which is a mux on the position bit.

The test that gives this meaning is
`an_opening_at_a_position_the_transcript_did_not_choose_is_refused`. The layer-0
Merkle tree is built from the input codeword alone, so it does not depend on the
transcript seed — which means a *genuine* opening at another position, against
the *same* root, can be handed to the verifier. The authentication path checks
out. Every earlier verifier in this project would have accepted it. The position
binding is what refuses it, and the test asserts both halves of that sentence:
the root assertions are met, the `lo_bit0 == i0` and `hi_bit0 == i0` assertions
are not.

## The lesson, restated

Determinacy rules out under-constrained outputs. It does not certify that an
output equals a canonical reduction, because that is a range property. The fix
was not a stronger determinacy analysis — it was a primitive (`bits`) that makes
the range property *expressible*, after which the determinacy system proves the
result in the ordinary way. The finding and its resolution are, in that order,
the argument for keeping the two concerns separate.
