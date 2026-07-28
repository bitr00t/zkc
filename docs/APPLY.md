# zkc — hygiene drop: the backend test suite stands on its own

No new capability. This drop fixes the thing that would stop anyone else from
reproducing the project at all, hardens the tests that hid the fault, and
corrects two claims in the checkpoint that had quietly stopped being true.

## The build bug

`stark_tests.rs` and `stark_poseidon_tests.rs` began

    const ISZERO_IR: &str = include_str!("/tmp/iszero.ir.json");

An absolute path into `/tmp`, left over from a session where the frontend had
just written it there. **A fresh clone does not compile** — `cargo test` fails
before running anything, and the failure names a file the reader has never
heard of. It is the first thing a reader following the write-up would hit.

## The fix, and why it is shaped this way

Real frontend output belongs in the tests — that is the point of those tests.
But there are two wrong ways to get it, and the repo had one of each:

- *An absolute path at build time* makes `cargo test` depend on a GHC toolchain
  and on one machine's `/tmp`.
- *A pasted JSON literal* drifts. `core_tests.rs` carried a copy of the IsZero
  IR whose line numbers no longer matched `examples/iszero.zkc`, and a test
  asserting a violation is reported at "line 26" that had been passing against
  a circuit the compiler stopped emitting some time ago.

So: the fixtures are **committed** under `backend/zkc-core/tests/fixtures/` —
`cargo test` needs no GHC, no network, no absolute path — and
`scripts/fixtures.sh --check` proves they are byte-for-byte what the frontend
emits today. The emitter is deterministic, so the check is a plain `cmp`.

Migrated (each verified to parse identical to its source's current output):

| fixture | source |
|---|---|
| `iszero.ir.json` | `examples/iszero.zkc` |
| `index_from_challenge.ir.json` | `examples/index_from_challenge.zkc` |
| `fri_verify_full.ir.json` | `examples/fri_verify_full.zkc` |
| `fri_verify_fs.ir.json` | `examples/fri_verify_fs.zkc` |

Hand-written IR stays inline and is deliberately *not* under the script: the
per-rule specs in `lowering_faithfulness_tests`, and the negative fixtures in
`core_tests` (`ISZERO_BROKEN`, `LINEAR`, `WIDESUM`, `MULSQUARE`, `FRI_FOLD`).
No source compiles to those — they are spec artefacts, and a script that tried
to regenerate them would be lying.

## The silent no-op — the real finding

Swapping `core_tests`' pasted literal for the committed fixture broke six
tests, and the reason is worth keeping. Those tests break a valid IR with
`str::replace` and assert the loader rejects it. The patterns were written
against the pretty-printed literal (`"schema_version": 2`); the emitter writes
compact JSON (`"schema_version":2`). Against real output **every one of those
replacements matched nothing** — the tests would have loaded valid, unmodified
IR and asserted that it was rejected.

That failure mode is worse than the one it replaced: a `replace` that matches
nothing is silently a no-op, so the same class of test could pass for years
while checking nothing. All such surgery now goes through

    fn mutate(src: &str, from: &str, to: &str) -> String  // asserts the pattern is present

so a formatting change in the emitter fails loudly, at the mutation, instead of
turning a rejection test into a tautology.

## Also in this drop

- **Four `unused import` warnings** removed from `goldilocks_tests.rs`
  (`TwoAdicField`, and `Field`/`Zero`/`One` from arkworks). The checkpoint's
  "zero warnings" is true again.
- **`scripts/run_all.sh`** runs the fixture check as step 0.
- **`docs/CHECKPOINT.md`** — repo-map drift corrected (`examples/` is at the
  repo root, not under `compiler/`; `README_phase7.md`, not `phase7.md`), and
  §4's SMT boundary rewritten, because it is no longer a boundary:

## SMT is runnable after all

§4 recorded that no solver was installable and the phase-3B escalation could
not be exercised. `apt-get install z3` (Ubuntu universe, z3 4.8.12) works, and
the path runs end to end:

    zkc build f.zkc -o /dev/null --smt-solver z3 --smt-dialect int --smt-timeout 20

On `gadget sqrt_g(x: field) -> (out: field) { assert out * out == x; }` the
decidable core stalls, z3 refutes, and the compiler prints the forgery it
built: `x = 4` with `out = 2` versus `out = -2`. The **refutation** half of the
SMT work — the half that had never been observed working — is confirmed.
`--smt-dialect int` is required: z3 has no finite-field theory, and cvc5, the
default and the only solver with native `QF_FF`, is still not packaged for
Ubuntu.

## Build / test

    scripts/fixtures.sh --check                                  # 4 ok
    cd backend && cargo test                                     # 122 green, no warnings
    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec              # 158/158

Test counts are unchanged (122 / 158) — nothing was added or removed, and
that is the point: the same suite, now reproducible from a clean clone.

## Notes

- Supersedes the previous drop's `APPLY.md` (the `bits` hint).
- Toolchain, confirmed again on Ubuntu 24.04: GHC 9.4.7 and cargo 1.75.0 both
  install from the distro archive; the frontend needs only boot libraries.
- Local-only `backend/Cargo.lock` pins remain required and are **not** part of
  this patch: `zeroize 1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`,
  `rayon-core 1.12.1`.
