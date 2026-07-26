# zkc — Phase 7, O: the complete in-circuit FRI verifier

O.1 expressed the algebraic fold as a determinate circuit; O.2 proved one fold
inside an outer proof. This closes O's larger arc: a *complete* FRI verifier for
one query, including the part O.1/O.2 left out — the **authenticity** check that
the openings really sit under the committed root.

**Prerequisite:** builds on O.1 (`fri_fold`), M (`mux`, `use` includes), and
phase 5 (the FRI/STARK prover). Supersedes O.1's `compiler/tests/Spec.hs`.

## The missing primitive: hashing in the language
A Merkle path is repeated hashing, so a verifier needs a hash it can run
in-circuit. The backend's default sponge nests `x^7` and blows past the
determinacy analysis' monomial budget, so this uses a **circuit-friendly** hash
of the same family, expressed as two gadgets:
- `std/hash_leaf.zkc` — `hash_leaf(v) = sbox(v + 1)`, `sbox(x) = x^7`.
- `std/compress.zkc` — `compress(l, r) = sbox(l + 2) + sbox(r + 3)`; order-sensitive,
  so left and right children hash differently.

Neither nests, so each proves determinate on its own; the Merkle walk composes
them through gadget *summaries*, which is what keeps the whole verifier under the
monomial budget. A matching `CircuitHash` drives the backend proof, so a path
that verifies in the tree verifies in the circuit, bit for bit.

## The verifier: examples/fri_verify_full.zkc
For one query of a small proof (domain 4, one fold round, depth-2 paths) the
circuit (a) Merkle-verifies both openings f(x) and f(-x) against the root —
hashing the leaf and walking the path, with the position bits choosing left/right
via `mux`; (b) folds the two openings (the O.1 relation); and (c) checks the fold
against the final codeword, which must be constant. All 16 intermediate results
are determined; "this query verifies" is an ordinary determinate circuit.

## Held honest end to end
- Frontend (`compiler/tests/Spec.hs`): `hash_leaf` and `compress` prove
  determinate and their under-constrained fixtures are rejected; the full
  verifier is proved determinate with all four includes resolved.
- Backend (`backend/zkc-core/tests/fri_verifier_tests.rs`): a real one-round FRI
  proof is produced and verified under `CircuitHash`; its first query's openings,
  authentication paths, challenge, and final codeword are fed to the verifier
  circuit, which is then **proved and verified as an outer STARK proof** —
  recursion over the whole query, paths included. Tampering a sibling makes the
  verifier reject and a forced outer proof fail to verify.

## Build / test
    make -C compiler all && cd compiler && ghc -O0 -isrc -itests \
        -outputdir build/test-objs -o build/spec tests/Spec.hs && ./build/spec   # 151/151
    cd backend && cargo test -p zkc-core --test fri_verifier_tests               # 2 green

## Notes
- Additive: the language, determinacy, SMT, both lowerings, the witness solver,
  and the phase-5 prover are unchanged; only gadgets and tests are added.
- **Scope, honestly.** One query, one round, depth-2 paths — the smallest
  instance that exercises every part (hash, path, fold, final). Fiat-Shamir
  (deriving the challenge and index in-circuit over the same hash) is the one
  remaining piece; the challenges are taken as inputs here. The structure scales
  by unrolling; a production verifier would add in-circuit Fiat-Shamir and more
  rounds/queries.
- Local-only `backend/Cargo.lock` pins remain required (never commit): `zeroize
  1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`, `rayon-core 1.12.1`.
