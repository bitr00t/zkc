# zkc — DEEP: the last core soundness boundary

Phase 5 shipped with one boundary marked rather than buried: FRI proved the
*quotient* low-degree, but the committed trace and grand-product `Z` columns
were never themselves tested. This closes it.

Backend 127 -> 133 tests. Frontend untouched (166). All green, no warnings.

## What was actually wrong

Not a bug — a spot check standing in for a proof.

The old verifier checked `composite = Q·Z_H` pointwise, at the positions the FRI
queries happened to open. Nothing anywhere asked the trace or `Z` to be
polynomials, and nothing looked at them at any position a query did not land on.
The query positions follow publicly from the commitment, so a prover could
simply retry until they missed whatever it wanted hidden.

## The construction

DEEP, and it moves where the constraint is checked.

An **out-of-domain point `ζ`** is drawn from the transcript after every
commitment — including the quotient's, which used to go straight into FRI
unbound and now needs a root, because the prover is about to make a claim about
it. The prover sends each column's value at `ζ`, and the composite identity is
checked **once, there**: one equation, off the domain, at a point the prover
could not know while committing.

That check binds nothing by itself — six invented values satisfying one equation
is easy. What binds it is the batch. For each committed column,

    (P(x) - P(ζ)) / (x - ζ)

is a polynomial *iff* `P` is a polynomial taking the claimed value at `ζ`: a
non-polynomial column has no low-degree quotient, and a polynomial column with a
lied-about value leaves a pole. These six quotients are combined with random
challenges and FRI tests the combination. One low-degree test now carries the
trace, `Z` and the quotient alike.

Each quotient enters scaled by `λ + λ'·x^e` rather than a plain `λ`. Without
that correction the batch is bounded by the largest degree in it, and a trace
column of a third that degree would pass a test it should fail. The exponent is
chosen per quotient so the padded term lands just inside the FRI bound.

`deep_batch` and `draw_ood_point` are each written once and called by both
prover and verifier. Two agreeing implementations of a random linear combination
is exactly the duplication that rots into a soundness bug nobody can see, since
each side stays self-consistent while both drift from the protocol.

## The test that gives it meaning

`deep_tests.rs`, built on a new `prove_with_corrupted_column` — exposed for the
same reason `prove_with_trace` was, because the tests that matter are the ones an
honest prover cannot express.

That prover is not a clumsy liar. It commits a column differing from the honest
low-degree extension at **one** position, and everything else is impeccable: the
quotient is genuinely low-degree, because it is built from the *uncorrupted*
column; every Merkle opening checks out, because the corrupted value is the
committed value; the constraint identity holds everywhere the old verifier
looked.

- `a_corrupted_column_is_refused_at_a_position_no_query_opens` — searches for a
  position the queries miss (a prover can grind for one), confirms no query
  opens it, and watches the proof be refused. The assertion is on the exact
  reason: the verifier gets past the constraint check at `ζ`, which passes, and
  dies in the low-degree test. What refuses the proof is not an inspection of
  the corrupted value but the fact that it is now inside FRI.
- `no_position_escapes_the_low_degree_test` — every position in the domain,
  refused. A spot check has positions it does not look at, by construction; this
  does not. The difference between the two protocols is the difference between
  *probably caught* and *caught*.
- `the_corruption_mechanism_itself_changes_nothing` — a corruption of zero must
  leave an honest proof honest, or the tests above would only be proving the
  alternative code path is broken.
- `an_invented_out_of_domain_value_is_refused` — all six slots, one at a time.
- `the_quotient_commitment_is_bound_to_the_transcript`.

## What it cost

**Seven field elements. 56 bytes.**

One commitment plus six out-of-domain values. The per-query openings did not
grow at all: the trace and `Z` were already opened there, and the rotated `Z`
opening the old protocol carried is gone — the rotation is handled at `ζ` now —
so the quotient opening takes its place. Prover-side, one Merkle tree over the
quotient and one interpolation for the batch.

Worth recording plainly, since "we hardened it and the proof doubled" is what
people expect. The boundary closed for a constant, not a factor.

## Files

- `backend/zkc-core/src/stark.rs` — rewritten: out-of-domain draw, the OOD
  constraint check, the shared batch, quotient commitment. The old per-query
  composite reconstruction is gone, which also means the verifier evaluates the
  selector and permutation polynomials once instead of once per query.
- `backend/zkc-core/tests/deep_tests.rs` — new, 6 tests.
- `docs/phase5-status.md` — the boundary section kept as written with its
  resolution appended; the boundary being marked rather than buried is the part
  worth preserving.
- `docs/README_phase5.md`, `docs/benchmarks.md`, `docs/CHECKPOINT.md`.

## Build / test

    cd backend && cargo test                                     # 133 green, no warnings

## Notes

- Supersedes the previous drop's `APPLY.md` (the gadget reference).
- The frontend is untouched: 0 `.hs` files changed, 166/166 checks pass. Phase 5
  claimed the prover was a leaf under the compiler, and hardening it did not
  reach upward — which is the same measurement phase 5 opened with.
- Local-only `backend/Cargo.lock` pins remain required and are **not** part of
  this patch: `zeroize 1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`,
  `rayon-core 1.12.1`.
