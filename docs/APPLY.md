# zkc — Phase 7, O.1 (a verifier check, expressed in the language)

Phase 7's second half, O, makes a proof into something a circuit can check.
O.1's first increment is the smallest honest piece the design names: one FRI
folding step, written as an ordinary gadget and held to the same determinacy
proof as any circuit — so "the proof verifies" is not a trusted black box but a
determinate circuit.

**Prerequisite:** builds on M (the `std/` library and `use` includes) and on N.1
(the executable IR spec, used by the backend security test). Apply the earlier
phase-6/7 drops first; this supersedes M's `compiler/tests/Spec.hs` and N.3's
`backend/zkc-core/tests/core_tests.rs`.

## The verifier checks
- `std/fri_fold.zkc` — `fri_fold(p, m, beta, x) -> (folded)`. Given a FRI layer's
  openings at x and -x, the challenge, and the point, it computes the next
  layer at x^2: `2x*folded == x*(p+m) + beta*(p-m)`, witnessing `1/(2x)` with an
  inverse that doubles as a proof that `2x != 0`. The verifier's advice is thus
  quarantined and `folded` is *determined* by the openings — the whole point of
  writing a verifier this way. (Verified numerically to compute the true
  next-layer evaluation.)
- `std/rlc.zkc` — `rlc(a, b, r) -> (out) = a + r*b`, the random-linear-combination
  step a verifier uses to batch many claims under a challenge.
- `examples/fri_verify.zkc` — a two-round FRI-query verifier: it folds across two
  layers and checks they agree (`layer1 == f1_x2`). Every output is determined
  by the proof openings, the challenges, and the query point.

## How it's held honest
- Frontend (`compiler/tests/Spec.hs`): `fri_fold` and `rlc` are added to the
  gadget suite — each proves determinate, and its under-constrained negative
  fixture is rejected. The two-round verifier is proved determinate end to end
  (resolving its `use std::fri_fold;`), and `fri_fold`'s generated reference is
  checked to show `folded` determined by a case split on x with `x != 0`
  guaranteed — the determinacy discipline, visible in the docs.
- Backend (`backend/zkc-core/tests/core_tests.rs`): held to the N.1 spec over
  BN254, the `fri_fold` circuit accepts the honest next-layer value and rejects a
  forged one, the spec naming the violated folding assertion. This is the
  security seam O.2's recursion will lean on.

## Build / test
    make -C compiler all
    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec        # 146/146 green
    cd backend && cargo test -p zkc-core                    # 50 core tests, all green

    ZKC_STD_PATH=std zkc build examples/fri_verify.zkc      # the verifier compiles

## Notes
- Additive: the language, determinacy, SMT, both lowerings, and the witness
  solver are unchanged; only gadgets and tests are added.
- The FRI fold is expressible in pure field arithmetic plus one inverse, so it
  proves under the decidable core — no SMT needed.
- Test progression: frontend 140 -> 146; backend 110 -> 111.
- Next: O.2 — feed a proof and its verification key to a verifier circuit and
  prove *that*, one proof attesting to another, with a tampered inner proof
  failing the outer.
