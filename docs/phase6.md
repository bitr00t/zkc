# Phase 6 — tooling: language server, profiler, gadget standard library

> Design note. Decisions are marked and overridable. As with every phase, the
> one measurement that shapes the work is stated first — and here it forces an
> honest break with a rule the last four phases held.

## The measurement, and the rule it breaks

Phases 2 through 5 all closed with the same line: *not one line of the frontend
changed*. That was the right invariant while the work was downstream of the
frontend — new arithmetizations, a new prover, all consuming the neutral IR the
frontend already emits. Phase 6 is different, and pretending otherwise would be
dishonest: **tooling for a language is frontend work.** A language server reads
source and reports diagnostics at positions; a profiler attributes cost back to
source lines; a gadget library is written in the language itself. None of these
live downstream of the frontend.

So before designing, the question was not "can we avoid touching the frontend"
but "how much of the frontend already supports this, and what is the smallest
honest change." That was checked by reading what the frontend tracks and emits:

* **Lines are tracked end to end.** The lexer tags every token with its line
  (`tokLine`); the AST carries `pdLine`, `rqLine`, `gdLine`; IR assertions carry
  their line; diagnostics carry `diagLine`. So position-attributed tooling has a
  spine already.
* **But only lines — no columns, no spans.** A diagnostic points at a line, not
  a range. An editor underline wants `(start, end)`; the frontend cannot yet
  provide it.
* **Diagnostics are already a structured record** — `Diagnostic { message, line,
  notes, help }` — but rendered only to a terminal string. There is no
  machine-readable form for an editor to consume.
* **Gadgets exist (phase 3) but there is no library** — no reusable definitions,
  and not one gadget example in `examples/`.
* **`zkc-stats` emits JSON but not per-line cost** — it totals constraints and
  rows, but does not attribute them back to the source that produced them.

This maps cleanly onto the smallest honest change per workstream, and it means
the frontend edits are *additive and narrow*: a JSON emitter beside the existing
renderer, a column added beside the existing line, a `use`-style include for
library gadgets. The determinacy type system — the project's whole thesis — is
already computed; phase 6 is largely about **surfacing** it, not recomputing it.

## What tooling is *for* here

A determinacy type system that makes under-constrained circuits a compile error
is only as valuable as its reach into a developer's hands. Phase 0–5 proved the
idea and built the machine; a proof that an output is under-determined is worth
far more as a red underline in an editor, the moment it is typed, than as a
line in a terminal after a full build. Phase 6 is where the thesis stops being
a compiler feature and becomes a working environment.

## Decision: surface, don't recompute; wrap, don't fork

Three sub-choices, each marked.

**The language server wraps the existing compiler, it does not reimplement it.**
The determinacy proof, the SMT escalation, the elaboration — all of it already
runs. The LSP server drives the same pipeline and translates its structured
diagnostics into the Language Server Protocol. Nothing about determinacy is
re-derived in the server; a second implementation would be a second thing to
keep correct. *Overridable:* incremental re-checking (only re-analysing the
edited region) is a performance layer that could later justify tighter
integration, but correctness comes from the one pipeline.

**The profiler is a view over data the backend already produces.** Phase 4's
`zkc-stats` measures both arithmetizations; phase 5 added proof-size and timing.
The profiler's new work is *attribution* — mapping each constraint or row back
to the source construct that produced it, via the `origin` string the lowering
already attaches to every row. The measurement exists; the profiler makes it
answer "which line is expensive," not just "how expensive is the whole circuit."

**The gadget standard library is written in the language, reviewed as code.**
The gadgets are `.zkc` source, not compiler built-ins, so they are checked by
the same determinacy analysis as user code — the library cannot smuggle in an
under-constrained gadget, because the compiler would reject it. This is the
strongest possible statement of the thesis: even the standard library is held
to it.

## Workstreams

### J — Machine-readable diagnostics and columns (the frontend groundwork)

Everything else depends on the frontend speaking a structured dialect, so this
comes first.

**J.1 — JSON diagnostics.** A `--json` (or `--diagnostics=json`) mode that emits
the `Diagnostic` record as JSON instead of rendering it to a terminal:
`{message, line, column?, severity, notes, help}`. This is a new emitter beside
the existing `render`, not a change to how diagnostics are produced — the same
record, a second serialisation. Tested by round-tripping every existing
diagnostic (determinacy failure, refutation, residual) through JSON and checking
the fields survive.

**J.2 — Column spans.** Thread a column through the lexer beside the line, and a
`(start, end)` span through the AST for the constructs diagnostics point at
(outputs, assertions, gadget calls). This is the one genuinely invasive frontend
change, and it is bounded: the lexer already walks characters, so a column
counter is a small addition, and spans are only needed where a diagnostic can
land. Tested by checking a diagnostic's span covers exactly the offending token
in a set of known-bad fixtures.

### K — The language server

**K.1 — LSP server over the pipeline.** A server (in Haskell, reusing the
compiler as a library) speaking the Language Server Protocol: on open/change,
run the pipeline, translate structured diagnostics to LSP diagnostics with
spans. Publishes determinacy errors, refutations (with the forged witness as the
diagnostic's related information), and residual-unknown warnings. Tested against
the LSP wire format with scripted open/change/diagnostic exchanges — no editor
needed, just the protocol.

**K.2 — Hovers and determinacy lenses.** The value-add unique to this language:
hovering an output shows *why* it is determined — the case split the proof used
(the `--explain` output, already computed, surfaced inline). A gadget call shows
its determinacy summary. An under-determined output gets a code lens naming the
branch where uniqueness fails. This is the determinacy type system made visible
at the point of use, which is the whole reason the phase exists. Tested by
asserting the hover text for known constructs matches the proof's explanation.

### L — The constraint-count profiler

**L.1 — Per-source-line attribution.** Extend the lowering's `origin` tracking
so every R1CS constraint and every Plonkish row carries the source line (and
span, from J.2) it came from, and aggregate cost by line. The backend already
attaches an origin string; this makes it a structured back-reference and sums
per line. Tested by checking the per-line costs sum to the totals `zkc-stats`
already reports, and that a known circuit attributes its multiplication to the
right line.

**L.2 — The profile report and editor integration.** A `zkc-profile` view (text
and JSON) ranking source lines by constraint/row cost across both
arithmetizations — "line 22 costs 8 constraints / 8 rows, the most in this
circuit" — and, through the LSP, an inlay hint showing each line's cost in the
editor. This is phase 4's cost model and phase 5's measurements brought to where
the code is written. Tested on circuits with a known hot line.

### M — The gadget standard library

**M.1 — Core gadgets, in the language.** A `std/` of reviewed `.zkc` gadgets for
the operations circuits reach for repeatedly: `is_zero`, `is_equal`, boolean
constraints (`assert_bit`), conditional select (`mux`), small-range checks,
bit decomposition. Each is ordinary source, proved determinate by the same
analysis as user code — the library is not trusted, it is *checked*. Tested by
compiling each gadget and asserting the determinacy proof succeeds, plus a
negative fixture per gadget showing the under-constrained version is rejected.

**M.2 — Includes and a documented interface.** A minimal `use std::is_zero;`
include mechanism so a circuit can pull a library gadget, and a generated
reference (from the gadgets' own determinacy summaries) documenting each
gadget's inputs, outputs, and what it constrains. Tested by a circuit that
includes a std gadget and compiles end to end, and by checking the generated
docs match the gadgets' actual summaries.

**Order: J → (K, L in parallel) → M.** J is the groundwork both K and L need
(structured diagnostics, spans, per-line origins). K and L are independent views
over that. M depends on the include mechanism but not on the editor tooling, and
can land any time after J; it is placed last because it is the most
language-design work and benefits from the tooling being in place to dogfood it.

## What it costs to the "frontend untouched" invariant

This is the phase where that invariant retires, and it should retire honestly
rather than be quietly redefined. The frontend changes in phase 6 are:
J.1 (a JSON emitter), J.2 (columns and spans), K (the server, as a new library
consumer of the compiler), and M.2 (an include mechanism). Each is additive —
no existing diagnostic, proof, or lowering changes behaviour — and each is
tested to preserve what phases 0–5 established. The discipline that replaces
"don't touch the frontend" is: **every frontend change is additive and
regression-tested against the existing 90 frontend checks.** The determinacy
analysis, the SMT layer, and the two arithmetizations must behave identically
after phase 6 as before it.

## Scope, drawn on purpose

- **One editor-agnostic server, not editor plugins.** Phase 6 delivers an LSP
  server speaking the standard protocol; a VS Code extension or Neovim config is
  a thin client anyone can write against it, not core work.
- **The profiler attributes, it does not optimise.** It says which line is
  expensive; automatically rewriting circuits to be cheaper is out of scope
  (and would need care, given determinacy must be preserved by any rewrite).
- **The std library is small and core, not comprehensive.** Enough gadgets to
  prove the model and cover common needs; a broad cryptographic gadget library
  (hashes, signatures) is its own project, downstream of this.
- **No incremental re-analysis.** The server re-runs the pipeline per change;
  for the circuit sizes this language targets that is fast enough, and
  incrementality is a performance layer for later.
- **Formal verification of the lowering stays in phase 7.** The profiler and
  server increase trust in *use*; proving the lowering correct is the next
  phase's job.

## What "done" looks like

1. `--json` diagnostics carrying the full structured record, round-trip tested.
2. Column spans through lexer and AST, covering the constructs diagnostics point
   at.
3. An LSP server publishing determinacy diagnostics with spans, driven by the
   real pipeline.
4. Hovers and lenses surfacing the determinacy proof (the `--explain` data) at
   the point of use.
5. Per-source-line cost attribution whose sums match `zkc-stats`, in a
   `zkc-profile` report and as editor inlay hints.
6. A `std/` of core gadgets, each proved determinate by the same analysis, each
   with a negative fixture showing the broken version is rejected.
7. An include mechanism and generated gadget reference.
8. **Every frontend change additive and regression-tested** — the 90 frontend
   checks and the determinacy/SMT/arithmetization behaviour unchanged.
