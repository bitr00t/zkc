# zkc — the gadget reference, actually generated

A small drop with a correction in it.

The previous note recorded that `std/REFERENCE.md` documents 5 of the 13 stdlib
gadgets and that no CLI entry point regenerates it. The first half was true; **the
second was wrong.** `zkc doc` has existed since phase 6 and does exactly this. It
was simply missing from the usage text — undiscoverable — and nobody had re-run
it since the phase-7 gadgets landed. The defect was staleness plus invisibility,
not a missing feature.

Frontend 164 -> 166 checks. Backend untouched (127). All green, no warnings.

## What changed

- **`zkc doc` is in `--help`**, with the invocation spelled out. That is the
  whole reason it went unused for two phases.
- **`std/reference.zkc`** — new. `zkc doc` reports on the gadgets *in scope*, and
  a scope is a program, so summarising the whole library needs one program that
  uses the whole library. This is that program:

      zkc doc std/reference.zkc --field goldilocks -o std/REFERENCE.md

  It earns its place twice. Because every gadget is resolved and proved here
  together, the file is also the library's integration check: all thirteen must
  parse, resolve, elaborate and prove determinate in a single scope — which no
  per-gadget check establishes.
- **`std/REFERENCE.md` regenerated** — 5 sections to 13. The eight that were
  missing are the whole of phase 7's stdlib work plus `range8`.
- **Two frontend checks**, applying the discipline `scripts/fixtures.sh --check`
  already applies to the IR fixtures:
  - `REFERENCE.md is exactly what zkc doc generates` — byte for byte. Verified
    to *fail* on drift, by perturbing the committed file and watching the suite
    go 165/166, not merely verified to pass.
  - `the generated reference does not depend on the field` — the document is
    committed once, for one field, so it had better not depend on which. It does
    not: rendering over bn254 and over Goldilocks gives identical output, since
    signatures, case splits and nonzero facts are the same in both. That is what
    makes committing a single file legitimate rather than a quiet assumption.

## Why bother

`Reference.hs` opens by claiming its output "is generated, never hand-written,
so it cannot fall out of step with the code." The claim had been false for two
phases: the code moved, the document did not, and nothing noticed. Regenerating
it would have fixed today's copy and left the claim just as unenforced. The
check is the part that makes the sentence true.

## Build / test

    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec              # 166/166
    ./compiler/build/zkc doc std/reference.zkc --field goldilocks -o std/REFERENCE.md
    git diff --exit-code std/REFERENCE.md                        # no drift

## Notes

- Supersedes the previous drop's `APPLY.md` (closing the in-circuit query index).
- `docs/CHECKPOINT.md` §4 loses the stale-reference item, §5 loses its second
  follow-up, and the repo map gains `std/reference.zkc` and the `doc` subcommand.
- Backend and `Cargo.lock` are untouched by this drop; the local-only pins remain
  as documented in §6.
