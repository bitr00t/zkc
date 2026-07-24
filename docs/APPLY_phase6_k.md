# zkc — Phase 6, K (language server + hover)

An LSP server that reuses the compiler as a library to publish determinacy
diagnostics, plus a hover that surfaces the `--explain` proof.

**Prerequisite:** this builds on J.1 (JSON diagnostics, `Zkc.Json`) and J.2
(columns, `diagCol`) from the previous drop (`zkc_phase6_j1_j2.zip`). Apply that
first; the files below overlay cleanly on top of it (they supersede that drop's
`Main.hs` and `tests/Spec.hs`).

## New files
- `compiler/src/Zkc/Diagnose.hs` — the front end as a library. `diagnoseSource`
  runs parse -> elaborate -> the *decidable* determinacy core (no solver, no
  IO) and returns `[Diagnostic]`; the CLI and the server now share the same
  diagnostic construction (the `determinacyDiagnostic` / `refutation` /
  `residual` builders moved here out of `Main`). Also `hoverAt`, which reports
  the determinacy proof for the output under the cursor.
- `compiler/src/Zkc/Lsp.hs` — the LSP server. Speaks JSON-RPC over stdin/stdout
  with `Content-Length` framing (UTF-8-byte-accurate, hand-rolled on the boot
  `bytestring`). `handleMessage` is a pure `(state, request) -> (state,
  replies)` function so the whole protocol is unit-tested without a subprocess;
  `runLsp` is only the IO loop. Handles `initialize` (advertising full sync +
  hover), `didOpen` / `didChange` / `didClose` (publishing diagnostics), and
  `textDocument/hover` (the proof), plus `shutdown` / `exit`.

## Modified
- `compiler/src/Main.hs` — the five diagnostic builders moved to `Zkc.Diagnose`
  (imported back); new `zkc lsp` subcommand wired to `runLsp`; usage updated.
  CLI behaviour is otherwise unchanged.
- `compiler/tests/Spec.hs` — +14 checks (LSP protocol core, diagnostic->LSP
  range mapping, UTF-8 framing, and hover surfacing the proof).

## Run / test
    make -C compiler all
    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec        # 121/121 green

    # start the server (an editor client speaks to it over stdin/stdout):
    compiler/build/zkc lsp

## Notes
- The server runs only the decidable core, so it never shells out to a solver
  and is safe to call on every keystroke. Refutation/residual (which need SMT
  and IO) keep their diagnostic builders in `Zkc.Diagnose` for the CLI path.
- Hover on an output shows "proved determined" with the case splits the proof
  used (e.g. `x == 0` / `x != 0`), or, for the output the proof got stuck on,
  why it is not determined.
- Baseline entering K was 107/107; K -> 121/121 (+14).
