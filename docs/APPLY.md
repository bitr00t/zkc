# zkc — polish: a gadget family, and the borrowed backend retired

Two items from §5, neither load-bearing. No core soundness boundary was open
before this drop and none is open after it.

Backend 133 -> 135 tests, frontend 166 -> 172 checks. All green, no warnings.

## 1. `canonical_low<k>` — the index gadget, generalised

`canonical_low2` returned the two low bits of a value's canonical
representative, which covers FRI domains of size 2 and 4. Everything in it
except the last two assertions is width-independent: the same 64-bit
decomposition, the same canonicity check. Only the exposure of the low bits
varies.

The language has no parametric gadgets — a gadget's arity is part of its
declaration — so the parameter has to live outside the language.
`scripts/gen_canonical.sh` is where it lives now, and it emits both the gadget
and its negative fixture for any width. Committed: k = 1, 2, 3, 4. The examples
need 1 and 2; 3 and 4 are there so that "generalised" is a claim with evidence
rather than a design intention.

This is the third generated artefact in the repo to get the same treatment, and
deliberately so: committed so the build stands alone, with a `--check` that
proves it is still what the generator produces (`scripts/fixtures.sh`, `zkc
doc`, and now this). `scripts/run_all.sh` checks both generators before it does
anything else.

What actually got tested, rather than merely regenerated:

- `the_derivation_widens_to_a_larger_domain` — sixteen candidate indices at
  domain 16, each walked against *every* 64-bit string congruent to the
  challenge, exactly as the domain-4 test does. Only the honest index survives.
- `the_canonicity_check_still_bites_at_the_wider_domain` — the wraparound does
  not go away when the domain grows. `p` is 1 mod every power of two up to
  `2^32`, so the wrapped string shifts the index by one at every width, and the
  same single obligation refuses it.
- The frontend suite checks all four widths over Goldilocks, each against a
  generated negative fixture (166 -> 172).

`examples/fri_verify_idx.zkc` now uses `canonical_low1`, which is what a
two-element domain actually wants — one bit is the whole position — and drops an
output it never used. `examples/index_from_challenge16.zkc` is the domain-16
counterpart of the sound example, and the only difference between the two files
is which gadget they `use`.

## 2. `zkc-prove` retired

The crate is gone. What it held was two different things:

- **The borrowed proving backend** — a bridge from our lowered R1CS into
  arkworks' Groth16, so phases 0-3 could show a complete source-to-proof
  pipeline without writing a prover. Phase 5 wrote one. This is deleted, along
  with `ark-groth16`, `ark-relations`, `ark-snark` and `ark-std`.
- **Tooling that only ever shared the crate with it** — `stats` (arithmetization
  cost accounting) and the binaries. Its own module doc said as much: *"It
  shares nothing with the proving path but the crate."* This moves to
  **`zkc-tools`**, which does no cryptography.

`zkc-prove` the binary becomes **`zkc-check`**: load IR, solve the witness,
lower to the chosen arithmetization, self-check. That is everything it did apart
from the Groth16 tail, and it is what the phase-4 claim the binary exists to
demonstrate actually needs — a circuit can be built either way, and the
determinacy record is identical on both paths. `arith_cli_tests` still drives
it; the one assertion that named Groth16 now names the self-check it was really
about. `zkc-stats` and `zkc-profile` are unchanged but for the crate name.

`ark-ff` and `ark-bn254` stay. They are how the project instantiates BN254,
which is half of the "everything is generic over the field" invariant, and the
differential oracle for the hand-written Goldilocks. Retiring a borrowed
*prover* is not the same as dropping a field.

## The toolchain fix, explained rather than repeated

Every checkpoint since phase 5 has carried four `cargo update --precise` lines
as a fix to reapply each session. They were never a defect in this repo.
`rust-toolchain.toml` pins **1.97.1**; with `rustup` installed, nothing needs
downgrading at all. The pins are what an *older* cargo needs — a distro one, and
Ubuntu 24.04 ships 1.75.0, which is what a container without `rustup` gets. The
exact cause, worth writing down once instead of rediscovering:

    feature `edition2024` is required
    The package requires the Cargo feature called `edition2024`, but that
    feature is not stabilized in this version of Cargo (1.75.0).

Retiring the Groth16 chain removed the two `rayon` pins outright. The two
`zeroize` pins remain, and only on an old cargo. §6 now says this instead of
listing four commands as though they were maintenance.

## Files

New: `scripts/gen_canonical.sh`, `std/canonical_low{1,3,4}.zkc` and their broken
fixtures, `examples/index_from_challenge16.zkc`.

Moved: `backend/zkc-prove` -> `backend/zkc-tools`; `src/bin/zkc-prove.rs` ->
`src/bin/zkc-check.rs`.

Deleted: the `LoweredCircuit` arkworks bridge and the Groth16 setup/prove/verify
path.

Changed: `std/canonical_low2.zkc` (now generated), `std/reference.zkc` and the
regenerated `std/REFERENCE.md` (13 -> 16 gadgets), `examples/fri_verify_idx.zkc`,
`compiler/tests/Spec.hs`, `scripts/{run_all,fixtures}.sh`,
`backend/zkc-core/tests/{index_binding,fri_verifier}_tests.rs`, docs.

## Build / test

    scripts/gen_canonical.sh --check                              # 8 ok
    scripts/fixtures.sh --check                                   # 7 ok
    cd backend && cargo test                                      # 135 green
    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec               # 172/172

## Notes

- Apply **after** `zkc-deep.patch`; this drop is built on it and both touch
  `docs/CHECKPOINT.md`.
- The Groth16 comparison in `docs/benchmarks.md` is now a historical
  measurement, labelled as such. The code that produced it is in the history.
- Local-only lock pins, on an old cargo only: `zeroize 1.8.1`,
  `zeroize_derive 1.4.2`.
