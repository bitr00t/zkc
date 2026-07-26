# zkc — Phase 7: the `bits` decomposition hint (language primitive)

Adds `bits`, the language's third advice form after `inv`/`inv_or_zero`. It
decomposes a value into its low bits and emits the constraints that pin them —
the primitive the standard library flagged as missing, and the one the sound
in-circuit query index was waiting on. Touches the frontend end to end
(syntax -> determinacy) and the backend witness solver.

## Syntax
    advice (b0, b1, .., bk) = bits(x);
Binds k+1 names to x's low bits (least significant first), inside a gadget.

## Frontend
- `Ast.hs` — new `HintBit Expr Int` (bit i of x); produced only by desugaring.
- `Parser.hs` — parses the tuple form and desugars it into primitives: one
  single-bit advice per name, a `b_i*(1-b_i)==0` constraint each, and the
  reconstruction `x == b0 + 2*b1 + ..`. No new elaborator machinery.
- `Ir.hs` / `Emit/Json.hs` — hint kind `KBits i`, emitted as
  `"hint":"bits","bit":i`.
- `Elaborate.hs` — `HintBit e i -> (KBits i, e)` in both advice paths.
- `Determinacy.hs` — the `closeBits` rule: once a bits node's source is
  determined, so are its bits (binary decomposition is injective on [0,2^n)).
  A marking, not a search — no SMT, and it scales (32- and 62-bit decompositions
  prove as readily as 2-bit). Wired into both the flat and compositional passes.

## Backend
- `ir.rs` — the hint node now carries `hint: String` + `bit: Option<u32>`
  (was a `HintKind` enum). Backward-compatible: inv/inv_or_zero still parse.
- `witness.rs` — solves a bits hint as bit `i` of the argument's canonical
  representative.

## What it unlocks
- `std/range8.zkc` — a general `2^n` range check, replacing the membership
  product that only scaled to tiny sets. The reconstruction forces the value
  into `[0, 2^n)`; `bits_tests` shows out-of-range values rejected.
- The range check the in-circuit query index needs — see the updated
  `docs/in-circuit-index.md` (the binding no longer waits on a missing
  primitive; one field-wraparound subtlety remains, itself now expressible).

## Build / test
    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec        # 158/158
    cd ../backend && cargo test -p zkc-core --test bits_tests   # 3 green
    cargo test -p zkc-core                                       # full suite green

## Notes
- Design notes: `docs/bits-hint.md` (the primitive), `docs/in-circuit-index.md`
  (updated status).
- Supersedes the prior drop's `Spec.hs`, `ir.rs`, `witness.rs`,
  `in-circuit-index.md`, `ROADMAP.md`, and `assert_range4.zkc` (comment only).
- Test progression: frontend 155 -> 158; backend 119 -> 122.
- Local-only `backend/Cargo.lock` pins remain required (never commit): `zeroize
  1.8.1`, `zeroize_derive 1.4.2`, `rayon 1.7.0`, `rayon-core 1.12.1`.
