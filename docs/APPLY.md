# zkc — Phase 6, J.1 (JSON diagnostics) + J.2 (columns & spans)

Overlay these onto the repo root (`bitr00t/zkc`), preserving paths. Frontend
only; the backend is untouched.

## New file
- `compiler/src/Zkc/Json.hs` — a tiny dependency-free JSON model (value type,
  encoder, parser). The structured-output foundation the rest of phase 6
  (LSP, profiler) builds on. Boot libraries only.

## Modified
- `compiler/src/Zkc/Diagnostics.hs`
    * J.1: `renderJson` / `parseDiagnostic` / `diagnosticToJson` /
      `diagnosticFromJson` — a diagnostic serialises to JSON and round-trips.
    * J.2: new `diagCol` field + `diagAtCol`; `render` now draws a caret under
      the offending column and shows a `line:col` locus.
- `compiler/src/Main.hs`
    * `--error-format human|json` (default human); all four error sites route
      through one `emitDiagnostic` helper.
    * The determinacy diagnostic now points a column (from the output atom).
- `compiler/src/Zkc/Syntax/Lexer.hs` — every token carries a 1-based `tokCol`;
  columns reset on newline.
- `compiler/src/Zkc/Syntax/Parser.hs` — syntax errors are pinned to the
  offending token's column; output/assert/instance nodes capture their column.
- `compiler/src/Zkc/Syntax/Ast.hs` — `pdCol` on `ParamDecl`; a column on
  `SAssert` and `SInstance` (the three sites where diagnostics land).
- `compiler/src/Zkc/Core/Ir.hs` — `iiCol` on `IrInput` (0 = unknown).
- `compiler/src/Zkc/Core/Elaborate.hs` — threads `pdCol` -> `iiCol` so the
  determinacy diagnostic can point at the output declaration.
- `compiler/tests/Spec.hs` — +17 checks (8 for J.1, 9 for J.2).

## Build / test
    make -C compiler all
    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec     # 107/107 green

## Notes
- Additive: the IR JSON emitter (`Emit/Json.hs`) and its schema v2 are
  untouched; `iiCol` is used only for diagnostics, not emitted into the IR.
- `diagnosticFromJson` expects the `col` field (it is always emitted, as
  `null` when absent), so J.1 and J.2 round-trip together.
- Baseline was 90/90; J.1 -> 98, J.2 -> 107.
