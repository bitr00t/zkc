# zkc — closing the in-circuit query index

Phase 7 left a finding rather than a feature: the natural in-circuit derivation
of the FRI query index is *proved determinate* and is *forgeable*. This drop
closes it, and then wires the result into a verifier that no longer trusts
anything about its own query.

Backend 122 -> 127 tests, frontend 158 -> 164 checks. All green, no warnings.

## The gadget

`std/canonical_low2.zkc` — the two low bits of a value's canonical
representative, which is the FRI query position for a domain of size 2 or 4.

The fix is not the one the previous checkpoint anticipated. That plan was to
range-check `high` in `challenge == index + domain*high`, now that `bits` makes
the range expressible. Given the primitive, a better move appears: stop
*relating* the index to the challenge and *read it off*. Decompose the challenge
into all 64 of its bits; the reconstruction the desugaring emits,

    challenge == b0 + 2*b1 + 4*b2 + ... + 2^63*b63

leaves the prover no freedom at all, and the range bound on the upper bits comes
for free, because they are themselves a `bits` decomposition. The index is then
`b0` (domain 2) or `b0 + 2*b1` (domain 4), read rather than derived.

`closeBits` proves the whole thing determinate with **no case split and no
SMT** — a 64-bit decomposition is a marking, not a search. That is what makes
the shape reachable at all.

## The wraparound, which is not a footnote

Goldilocks wraps at `p = 2^64 - 2^32 + 1`, which is *below* `2^64`. So a 64-bit
string is **not** a unique representative: whenever the canonical value `c` is
below `2^64 - p = 2^32 - 1`, the string for `c + p` is also 64 bits wide and
also satisfies the reconstruction — with different low bits. A prover holding
that second string moves the query index. It happens for about one challenge in
`2^32`. Rare is not sound.

The non-canonical strings are exactly `[p, 2^64)`, and the shape of `p` makes
that interval exactly describable: top 32 bits all set, low 32 bits not all
zero. One constraint refuses all of them and no canonical one:

    (all top bits set) * (low 32 bits) == 0

The all-ones test is a product of the 32 top bits — 31 multiplications, no
advice, no case split, so the gadget stays inside the decidable core. An
`is_zero` on `2^32-1 - hi` would cost three constraints instead of 31, at the
price of a case split and an inverse hint.

## Proved by enumeration, not by assertion

`index_binding_tests.rs`. The prover's entire freedom is the choice of bit
string, and at most two strings are congruent to any challenge (`c` and `c + p`;
`c + 2p` never fits 64 bits). So the tests walk *all* of them against *all* four
claimed indices — this is exhaustion over the attack surface, not a spot check.

- `the_sound_binding_accepts_exactly_the_honest_index` — for an ordinary
  challenge, a small one, `2^32 - 2` (the largest that wraps), `p - 1` and `0`:
  exactly one witness survives, with the challenge's low bits as its index.
- `the_forged_index_that_satisfies_the_naive_binding_is_now_refused`.
- `the_canonicity_check_is_the_load_bearing_constraint` — the sharpest wrap
  case, `c = 2^32 - 2`, whose alternative string is the all-ones `2^64 - 1`.
  Every bit is a bit, the reconstruction holds, the claimed index matches the
  supplied bits, and **exactly one** obligation refuses the witness. Drop that
  assertion and the circuit accepts two indices.

`naive_index_binding_is_determinate_but_unsound` stays, still passing, still
showing all four indices satisfying the old binding. The contrast is the point.

## The verifier that trusts nothing about its query

`examples/fri_verify_idx.zkc`. `fri_verify_fs.zkc` derives the fold challenge
but still accepts the *position* it is asked to check — and a prover that
chooses where it is opened is a prover that is not being tested. Now the
position is drawn from the transcript after the final codeword is absorbed
(`std/fs_index_challenge.zkc`, verified bit-exact against the real transcript),
reduced by `canonical_low2`, and everything it touches is bound to it: the
Merkle path bits of both openings, and the evaluation point `x`, which is a mux
on the position bit.

The test that gives this meaning is
`an_opening_at_a_position_the_transcript_did_not_choose_is_refused`. The layer-0
Merkle tree is built from the input codeword alone, so it does not depend on the
transcript seed — which means a **genuine** opening at another position, against
the **same** root, can be handed to the verifier. The authentication path checks
out. Every earlier verifier in this project would have accepted it. The test
asserts both halves: the root assertions are met, and `lo_bit0 == i0` /
`hi_bit0 == i0` are not.

## Files

New:
- `std/canonical_low2.zkc`, `std/fs_index_challenge.zkc`
- `std/tests/canonical_low2_broken.zkc`, `std/tests/fs_index_challenge_broken.zkc`
- `examples/index_from_challenge_sound.zkc`, `examples/fri_verify_idx.zkc`
- two fixtures under `backend/zkc-core/tests/fixtures/`

Changed:
- `index_binding_tests.rs`, `fri_verifier_tests.rs` — the tests above.
- `compiler/tests/Spec.hs` — the stdlib harness now carries a **field per
  gadget** instead of assuming bn254, because these two gadgets are arithmetic
  about `p` and should be checked in the field they mean something in. Plus
  determinacy cases for both new circuits.
- `scripts/fixtures.sh` — per-source compiler flags (`--field goldilocks`).
- `docs/in-circuit-index.md` — rewritten; status closed, kept in the order
  things happened because the order is the argument.
- `docs/CHECKPOINT.md` — §2, §3, §4, §5, §7.

## Noted, not fixed

`std/REFERENCE.md` documents 5 of the 13 stdlib gadgets — the phase-7 additions
were never added. It calls itself generated from determinacy summaries, but no
CLI entry point regenerates it; `renderReference` is reachable only from the
test suite. Either wire up a `zkc reference` subcommand and regenerate, or stop
calling it generated. Recorded in §4 rather than patched here, to keep this drop
about one thing.

## Build / test

    scripts/fixtures.sh --check                                  # 6 ok
    cd backend && cargo test                                     # 127 green, no warnings
    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec              # 164/164

## Notes

- Supersedes the previous drop's `APPLY.md` (the test-suite hygiene pass).
- The two Goldilocks circuits must be compiled with `--field goldilocks`;
  `scripts/fixtures.sh` does this for them. The canonicity check is arithmetic
  about `p` and means nothing over another field.
- Local-only `backend/Cargo.lock` pins remain required and are **not** part of
  this patch: `zeroize 1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`,
  `rayon-core 1.12.1`.
