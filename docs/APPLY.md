# zkc — Phase 6, L (the constraint-count profiler)

Per-source-line cost attribution: a `zkc-profile` report (text and JSON) that
ranks source lines by the constraints and rows they produce, and, through the
language server, an inlay hint showing each line's cost.

**Prerequisite:** builds on J.1/J.2 (`Zkc.Json`, columns) and K (the LSP server,
`Zkc.Diagnose`, `Zkc.Lsp`). Apply `zkc_phase6_j1_j2.zip` and `zkc_phase6_k.zip`
first; the files here overlay on top and supersede K's `Diagnose.hs`, `Lsp.hs`
and `tests/Spec.hs`.

## L.1 — Per-source-line attribution
The mechanism: every R1CS constraint and every Plonkish row now carries the
source line it came from, and cost is aggregated by line. The per-line costs sum
to exactly the *unfused* totals `zkc-stats` already reports — the profiler is a
view over the same measurement, not a second one.

Attribution is done on the **unfused** lowering, where each constraint and row
maps 1:1 to the construct that produced it. Fusion is a cross-line rewrite with
no honest per-line split, so it is deliberately not what the profile attributes.

- Frontend: the IR node now carries a source line (`nLine`), threaded through
  elaboration and the optimiser and emitted in the IR JSON. Files:
  `compiler/src/Zkc/Core/{Ir,Elaborate,Passes}.hs`, `compiler/src/Zkc/Emit/Json.hs`
  (and a one-token pattern update in `Analysis/Determinacy.hs` and `Diagnose.hs`).
- Backend: `Node`, R1CS `Constraint` and Plonkish `Row` gain a `line`; the
  lowering tags mul constraints/rows with the node's line and assertion
  constraints/rows with the assertion's line. Files:
  `backend/zkc-core/src/{ir,r1cs,plonkish,lower}.rs` (plus `line: 0` in two
  STARK test row-builders).
- Aggregation: `zkc_prove::stats::profile` groups the unfused lowering by line.
  Tested (`backend/zkc-prove/tests/profile_tests.rs`) that per-line costs sum to
  `zkc-stats`'s unfused totals and that a multiplication is billed to its line.

## L.2 — The profile report and editor integration
- `zkc-profile` (`backend/zkc-prove/src/bin/zkc-profile.rs`): a new binary that
  ranks source lines by cost across both arithmetizations, text or `--json`,
  naming the hottest line. `Profile::{render_text,render_json,hottest}` live in
  the `stats` module.
- Inlay hints: the language server advertises `inlayHintProvider` and answers
  `textDocument/inlayHint` with each line's cost at end of line. Because the LSP
  is Haskell and cannot cheaply call the Rust profiler, `compiler/src/Zkc/Profile.hs`
  reproduces the same unfused accounting on the Haskell IR (the rules are the
  backend's, kept trivial so they cannot drift). `zkc-profile` remains canonical.

## Build / test
    make -C compiler all
    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec        # 126/126 green

    cd backend && cargo test                                # all green, incl.
    cargo build --bin zkc-profile                           #   profile_tests (4)
    zkc build circuit.zkc -o c.ir.json && \
      cargo run --bin zkc-profile -- c.ir.json              # per-line report

## Notes
- **Never commit `backend/Cargo.lock`.** Local-only pins needed to build under
  rustc 1.75: `zeroize 1.8.1`, `zeroize_derive 1.4.2`, and for the profiler/
  arkworks path `rayon 1.7.0` + `rayon-core 1.12.1` (rayon-core >=1.13 needs
  rustc 1.80).
- Cross-checked end to end: on a circuit whose line 6 holds two muls and an
  assertion and line 7 an add and an assertion, both `zkc-profile` and the LSP
  inlay hints report line 6 = 3 constraints / 3 rows, line 7 = 1 / 2, totalling
  the 4 / 5 unfused counts `zkc-stats` prints.
- Test progression: 121 (entering L) -> 126 frontend; backend +4 profile tests.
