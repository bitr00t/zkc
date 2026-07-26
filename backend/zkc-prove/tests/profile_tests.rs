//! Tests for per-source-line cost attribution (phase 6, Workstream L.1).
//!
//! The claim L.1 makes is an accounting identity: attributing every constraint
//! and every row to the source line that produced it must not lose or invent
//! cost. So the headline test is that the per-line costs sum back to exactly the
//! unfused totals `zkc-stats` already reports — the profiler is a *view* over
//! the same measurement, not a second one. The other test pins the attribution
//! itself: a multiplication on a known line is billed to that line.

use zkc_prove::stats::{measure_json, profile_json};

/// A circuit whose multiplication is on line 5 and is *not* fused (it feeds an
/// `add`, not an assertion directly), so it keeps its own constraint/row and
/// its line is observable.
const MUL_LINE_IR: &str = r##"{
  "schema_version": 2, "name": "MulLine", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "public"},
    {"wire": 2, "name": "b", "visibility": "public"},
    {"wire": 3, "name": "z", "visibility": "output", "line": 6}],
  "nodes": [
    {"wire": 4, "op": "mul", "line": 5, "args": [1, 2]},
    {"wire": 5, "op": "const", "line": 5, "value": "1"},
    {"wire": 6, "op": "add", "line": 5, "args": [4, 5]}],
  "assertions": [
    {"lhs": 3, "rhs": 6, "label": "z == a * b + 1", "line": 6}],
  "determinacy": {"proved": true, "targets": ["z"], "branches": [[]]}
}"##;

/// The is_zero gadget, whose assertions sit on lines 22 and 23. Its `mul`
/// nodes carry no line (they lower into the two assertions after fusion), which
/// makes it a good check that the sum identity holds even when some cost lands
/// on the "unknown" line 0.
const ISZERO_IR: &str = r##"{
  "schema_version": 2, "name": "IsZero", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "x", "visibility": "private"},
    {"wire": 2, "name": "out", "visibility": "output", "line": 20}],
  "nodes": [
    {"wire": 3, "op": "hint", "hint": "inv_or_zero", "name": "inv", "gadget": "is_zero", "args": [1]},
    {"wire": 4, "op": "mul", "args": [1, 3]},
    {"wire": 5, "op": "const", "value": "1"},
    {"wire": 6, "op": "sub", "args": [5, 2]},
    {"wire": 7, "op": "mul", "args": [1, 2]},
    {"wire": 8, "op": "const", "value": "0"}],
  "assertions": [
    {"lhs": 4, "rhs": 6, "label": "(x * inv) == (1 - out)", "line": 22},
    {"lhs": 7, "rhs": 8, "label": "(x * out) == 0", "line": 23}],
  "determinacy": {"proved": true, "targets": ["out"], "branches": [["x == 0"], ["x != 0"]]}
}"##;

/// The invariant: per-line costs sum to the unfused totals `zkc-stats` reports.
#[test]
fn per_line_costs_sum_to_zkc_stats_totals() {
    for ir in [MUL_LINE_IR, ISZERO_IR] {
        let profile = profile_json(ir).expect("profile");
        let report = measure_json(ir).expect("measure");

        let r1cs_sum: usize = profile.lines.iter().map(|l| l.r1cs).sum();
        let plonk_sum: usize = profile.lines.iter().map(|l| l.plonkish).sum();

        // The profile's own totals reproduce the sum...
        assert_eq!(r1cs_sum, profile.r1cs_total, "r1cs per-line sum vs profile total");
        assert_eq!(plonk_sum, profile.plonkish_total, "plonkish per-line sum vs profile total");

        // ...and equal the unfused totals the cost report already publishes.
        assert_eq!(
            profile.r1cs_total, report.r1cs_constraints_unfused,
            "r1cs total vs zkc-stats unfused constraints"
        );
        assert_eq!(
            profile.plonkish_total, report.plonkish_rows_unfused,
            "plonkish total vs zkc-stats unfused rows"
        );
    }
}

/// A multiplication is billed to the line it was written on.
#[test]
fn a_multiplication_is_attributed_to_its_line() {
    let profile = profile_json(MUL_LINE_IR).expect("profile");

    let line5 = profile
        .lines
        .iter()
        .find(|l| l.line == 5)
        .expect("line 5 should carry cost");

    // The unfused lowering emits exactly one R1CS constraint for the mul, and
    // that constraint is the only cost on line 5 in R1CS.
    assert_eq!(line5.r1cs, 1, "the multiplication is one R1CS constraint on line 5");

    // The assertion on line 6 is billed separately.
    let line6 = profile.lines.iter().find(|l| l.line == 6).expect("line 6");
    assert_eq!(line6.r1cs, 1, "the assertion is one R1CS constraint on line 6");

    // No cost is stranded on the unknown line: every constraint here has a line.
    assert!(
        !profile.lines.iter().any(|l| l.line == 0),
        "every constraint/row in this circuit should carry a source line"
    );
}

/// The text report ranks lines heaviest-first and names the hottest.
#[test]
fn render_text_ranks_lines_and_names_the_hottest() {
    let profile = profile_json(MUL_LINE_IR).expect("profile");
    let text = profile.render_text();

    // Line 5 (mul + const + add) outweighs line 6 (a single assertion), so it
    // is named the hottest and printed first.
    assert!(text.contains("hottest: line 5"), "hottest line named: {text}");
    let line5_at = text.find("  5").expect("line 5 present");
    let line6_at = text.find("  6").expect("line 6 present");
    assert!(line5_at < line6_at, "heaviest line ranked first");
    assert!(text.contains("by source line"), "has a header");
}

/// The JSON report carries the per-line array and the totals.
#[test]
fn render_json_has_the_per_line_shape() {
    let profile = profile_json(MUL_LINE_IR).expect("profile");
    let json = profile.render_json();

    assert!(json.contains("\"name\":\"MulLine\""));
    assert!(json.contains("\"lines\":["));
    assert!(json.contains("\"line\":5,\"r1cs\":1,\"plonkish\":3"), "line 5 entry: {json}");
    assert!(json.contains("\"r1cs_total\":2"));
    assert!(json.contains("\"plonkish_total\":4"));
}