# zkc — Phase 6, M (the gadget standard library)

A `std/` of reviewed `.zkc` gadgets, each ordinary source proved determinate by
the same analysis as user code, plus a `use` include mechanism and a generated
reference. The library is not trusted — it is *checked*: the compiler would
reject an under-constrained gadget, and each gadget ships with a negative
fixture proving it does.

**Prerequisite:** builds on J (structured diagnostics/spans), K (the LSP), and L
(per-line profiling). Apply `zkc_phase6_j1_j2.zip`, `_k.zip`, `_l.zip` first; the
files here overlay on top and supersede L's `Determinacy.hs` and `tests/Spec.hs`.

## M.1 — Core gadgets, in the language
Five gadgets under `std/`, each gadget-only source (a library file), each proved
determinate by the decidable core and each with an under-constrained negative
fixture under `std/tests/` that determinacy rejects:

- `is_zero(x) -> (out)`        — out = [x == 0]; proved by case split on x.
- `inverse(x) -> (inv_x)`      — inv_x = 1/x; exports the fact x != 0.
- `assert_bit(b) -> (out)`     — constrains b to {0,1}, returns it.
- `mux(sel, a, b) -> (out)`    — out = sel ? a : b; sel constrained to a bit.
- `assert_range4(x) -> (out)`  — small-range check: constrains x to {0,1,2,3}.

The tests (in `tests/Spec.hs`) read the shipped files, wrap each in a circuit,
and assert the good version proves and the broken version is rejected.

**Two gadgets from the design list are intentionally deferred.** `is_equal`
(zero-test on a - b) and general bit decomposition are not provable by the
decidable core: it case-splits on input *atoms*, so it proves `is_zero(x)` (x is
an atom) but not `is_zero(a - b)`, and bit decomposition needs a case analysis
the core does not do. Both are provable via SMT escalation, which needs a solver
(z3/cvc5) not present in this environment, so they are left out rather than
shipped untested. This matches the design's "small and core, not comprehensive"
scope; a decomposition *hint* primitive would let the range/bits family grow.

## M.2 — Includes and a documented interface
- **Include mechanism.** A `use std::is_zero;` prefix (new `use` keyword in the
  lexer, `UseDecl` in the AST, `pUses` in the parser). `Main` resolves each
  include by reading `<module>/<item>.zkc`, parsing it with the new library
  parser `parseGadgets`, and merging its gadgets into the program before
  elaboration (dedup by name). The `std` module resolves to `$ZKC_STD_PATH`, or
  `./std` by default.
- **Generated reference.** `zkc doc <file.zkc>` proves each gadget and renders
  its determinacy *summary* — signature, the case split the proof used, and any
  nonzero facts it requires or guarantees. Because it is generated from the same
  summaries the proof caches, it cannot drift from what was proved. The shipped
  `std/REFERENCE.md` is its output. New module: `compiler/src/Zkc/Reference.hs`;
  new export `gadgetSummaries` in `Analysis/Determinacy.hs`.

## Build / test
    make -C compiler all
    cd compiler && ghc -O0 -isrc -itests -outputdir build/test-objs \
        -o build/spec tests/Spec.hs && ./build/spec        # 140/140 green

    # include mechanism and reference, end to end:
    ZKC_STD_PATH=std zkc build mycircuit.zkc      # mycircuit.zkc: `use std::is_zero;`
    ZKC_STD_PATH=std zkc doc  mycircuit.zkc        # prints the gadget reference

## Notes
- **A build fix is included.** The working `Parser.hs` exported `parseGadgets`
  without defining it (a dangling export that broke the build). It is now
  defined — as the library parser M.2 needs — so the frontend links again.
- Every frontend change is additive: existing examples still compile, and the
  determinacy / SMT / arithmetization behaviour is unchanged. Test progression:
  126 (entering M) -> 140 (+2 include parsing, +10 std gadgets, +2 end-to-end).
- The std files carry no circuit (they are libraries); `zkc build` a circuit
  that `use`s them, or wrap them, to compile.
