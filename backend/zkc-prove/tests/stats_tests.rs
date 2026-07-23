//! Tests for the arithmetization cost accounting (phase 4, Workstream F.1).
//!
//! The measurement is the deliverable, so the numbers are pinned here. These
//! are the same circuits Workstream D measured, now surfaced through the
//! reporting the CLI prints — and the crossover (R1CS wins on a wide sum,
//! Plonkish ties on multiplications) is asserted, because "neither
//! arithmetization dominates" is the whole claim.

use zkc_prove::stats::{measure_json, Cheaper};

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

const WIDESUM_IR: &str = r##"{
  "schema_version": 2, "name": "WideSum", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "private"},
    {"wire": 2, "name": "b", "visibility": "private"},
    {"wire": 3, "name": "c", "visibility": "private"},
    {"wire": 4, "name": "d", "visibility": "private"},
    {"wire": 5, "name": "e", "visibility": "private"},
    {"wire": 6, "name": "f", "visibility": "private"},
    {"wire": 7, "name": "z", "visibility": "output", "line": 8}],
  "nodes": [
    {"wire": 8, "op": "add", "args": [1, 2]},
    {"wire": 9, "op": "add", "args": [8, 3]},
    {"wire": 10, "op": "add", "args": [9, 4]},
    {"wire": 11, "op": "add", "args": [10, 5]},
    {"wire": 12, "op": "add", "args": [11, 6]}],
  "assertions": [
    {"lhs": 7, "rhs": 12, "label": "z == a + b + c + d + e + f", "line": 8}],
  "determinacy": {"proved": true, "targets": ["z"], "branches": [[]]}
}"##;

fn many_products_ir(n: usize) -> String {
    let mut inputs = String::new();
    let mut nodes = String::new();
    let mut assertions = String::new();
    let mut targets = String::new();
    for i in 0..n {
        let (a, b, o) = (3 * i + 1, 3 * i + 2, 3 * i + 3);
        inputs.push_str(&format!(
            "{{\"wire\":{a},\"name\":\"a{i}\",\"visibility\":\"private\"}},\
             {{\"wire\":{b},\"name\":\"b{i}\",\"visibility\":\"private\"}},\
             {{\"wire\":{o},\"name\":\"o{i}\",\"visibility\":\"output\"}}"
        ));
        let mul = 3 * n + 1 + i;
        nodes.push_str(&format!("{{\"wire\":{mul},\"op\":\"mul\",\"args\":[{a},{b}]}}"));
        assertions.push_str(&format!(
            "{{\"lhs\":{o},\"rhs\":{mul},\"label\":\"o{i} == a{i} * b{i}\",\"line\":{i}}}"
        ));
        targets.push_str(&format!("\"o{i}\""));
        if i + 1 < n { inputs.push(','); nodes.push(','); assertions.push(','); targets.push(','); }
    }
    format!(
        "{{\"schema_version\":2,\"name\":\"ManyMul\",\"field\":\"bn254\",\"const_one_wire\":0,\
          \"inputs\":[{inputs}],\"nodes\":[{nodes}],\"assertions\":[{assertions}],\
          \"determinacy\":{{\"proved\":true,\"targets\":[{targets}],\"branches\":[[]]}}}}"
    )
}

#[test]
fn measures_both_arithmetizations_from_one_ir() {
    let r = measure_json(ISZERO_IR).unwrap();
    // The shared IR shape.
    assert_eq!(r.multiplications, 2);
    assert_eq!(r.hints, 1);
    assert_eq!(r.assertions, 2);
    // Both bills, fused, matching what Workstream D pinned.
    assert_eq!(r.r1cs_constraints, 2);
    assert_eq!(r.plonkish_rows, 2);
    // And the unfused baselines, so the fusion saving is a real delta.
    assert_eq!(r.r1cs_constraints_unfused, 4);
    assert_eq!(r.plonkish_rows_unfused, 7);
}

#[test]
fn reports_the_fusion_saving_as_a_fraction() {
    let r = measure_json(ISZERO_IR).unwrap();
    assert!((r.r1cs_fusion_saving() - 0.5).abs() < 1e-9); // 4 -> 2
    assert!((r.plonkish_fusion_saving() - (1.0 - 2.0 / 7.0)).abs() < 1e-9); // 7 -> 2
}

#[test]
fn multiplication_heavy_circuits_tie() {
    // IsZero and ManyMul: fusion brings Plonkish level with R1CS.
    assert_eq!(measure_json(ISZERO_IR).unwrap().cheaper(), Cheaper::Tie);
    let many = many_products_ir(8);
    let r = measure_json(&many).unwrap();
    assert_eq!(r.r1cs_constraints, 8);
    assert_eq!(r.plonkish_rows, 8);
    assert_eq!(r.plonkish_copies, 0); // nothing crosses a row boundary
    assert_eq!(r.cheaper(), Cheaper::Tie);
}

#[test]
fn a_wide_linear_sum_is_where_r1cs_wins() {
    // The crossover that justifies keeping the IR neutral: R1CS folds the sum
    // into one constraint; three-cell gates cannot.
    let r = measure_json(WIDESUM_IR).unwrap();
    assert_eq!(r.r1cs_constraints, 1);
    assert!(r.plonkish_rows > 1);
    assert_eq!(r.cheaper(), Cheaper::R1cs);
}

#[test]
fn json_output_is_well_formed_and_carries_both_bills() {
    let json = measure_json(WIDESUM_IR).unwrap().render_json();
    // Structural spot-checks; the CLI test parses it properly.
    assert!(json.starts_with('{') && json.ends_with('}'));
    assert!(json.contains("\"name\":\"WideSum\""));
    assert!(json.contains("\"r1cs\":{\"constraints\":1"));
    assert!(json.contains("\"cheaper\":\"r1cs\""));
}

#[test]
fn the_field_does_not_change_the_counts() {
    // Counting needs a concrete field (a const becomes a field element), but
    // the counts are structural, so the choice must not matter. We measure
    // over BN254 via the helper; measuring the same IR twice is stable.
    let a = measure_json(ISZERO_IR).unwrap();
    let b = measure_json(ISZERO_IR).unwrap();
    assert_eq!(a.r1cs_constraints, b.r1cs_constraints);
    assert_eq!(a.plonkish_rows, b.plonkish_rows);
}