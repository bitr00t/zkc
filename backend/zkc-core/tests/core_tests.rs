//! Backend tests.
//!
//! The IR fixtures below are written out by hand rather than produced by the
//! compiler. That is deliberate: these tests pin down the *contract* at the
//! Haskell/Rust boundary, so they must fail if the backend's reading of the
//! schema drifts, even when the frontend drifts with it. End-to-end agreement
//! between the two halves is covered separately by `scripts/run_all.sh`.

use std::collections::HashMap;

use ark_bn254::Fr;
use zkc_core::field::ZkField;
use zkc_core::ir::Ir;
use zkc_core::lower::lower;
use zkc_core::witness::{solve, SolveInputs};

// --- Fixtures ------------------------------------------------------------

const ISZERO_IR: &str = r#"{
  "schema_version": 1, "name": "IsZero", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "x", "visibility": "private"},
    {"wire": 2, "name": "out", "visibility": "public"}],
  "nodes": [
    {"wire": 3, "op": "hint", "hint": "inv_or_zero", "name": "inv", "args": [1]},
    {"wire": 4, "op": "mul", "args": [1, 3]},
    {"wire": 5, "op": "const", "value": "1"},
    {"wire": 6, "op": "sub", "args": [5, 2]},
    {"wire": 7, "op": "mul", "args": [1, 2]},
    {"wire": 8, "op": "const", "value": "0"}],
  "assertions": [
    {"lhs": 4, "rhs": 6, "label": "(x * inv) == (1 - out)", "line": 17},
    {"lhs": 7, "rhs": 8, "label": "(x * out) == 0", "line": 18}]
}"#;

/// The same circuit with the second assertion (and its nodes) removed.
const ISZERO_BROKEN_IR: &str = r#"{
  "schema_version": 1, "name": "IsZeroBroken", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "x", "visibility": "private"},
    {"wire": 2, "name": "out", "visibility": "public"}],
  "nodes": [
    {"wire": 3, "op": "hint", "hint": "inv_or_zero", "name": "inv", "args": [1]},
    {"wire": 4, "op": "mul", "args": [1, 3]},
    {"wire": 5, "op": "const", "value": "1"},
    {"wire": 6, "op": "sub", "args": [5, 2]}],
  "assertions": [
    {"lhs": 4, "rhs": 6, "label": "(x * inv) == (1 - out)", "line": 17}]
}"#;

/// Only linear operations, so lowering should emit no multiplication
/// constraints at all — one constraint per assertion and nothing else.
const LINEAR_IR: &str = r#"{
  "schema_version": 1, "name": "Linear", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "private"},
    {"wire": 2, "name": "z", "visibility": "public"}],
  "nodes": [
    {"wire": 3, "op": "const", "value": "3"},
    {"wire": 4, "op": "add", "args": [1, 3]},
    {"wire": 5, "op": "neg", "args": [4]},
    {"wire": 6, "op": "sub", "args": [1, 5]}],
  "assertions": [
    {"lhs": 2, "rhs": 6, "label": "z == a - (-(a + 3))", "line": 5}]
}"#;

fn inputs(pairs: &[(&str, &str)]) -> HashMap<String, Fr> {
    pairs
        .iter()
        .map(|(name, value)| ((*name).to_string(), Fr::from_decimal(value).unwrap()))
        .collect()
}

fn run(ir: &Ir, given: &[(&str, &str)], advice: &[(&str, &str)]) -> (Vec<Fr>, Vec<String>) {
    let given = inputs(given);
    let advice = inputs(advice);
    let wire_values = solve(ir, &SolveInputs { inputs: &given, advice_overrides: &advice }).unwrap();
    let r1cs = lower::<Fr>(ir).unwrap();
    let assignment = r1cs.assignment(&wire_values);
    let origins = r1cs.check(&assignment).into_iter().map(|v| v.origin).collect();
    (wire_values, origins)
}

// --- Field ---------------------------------------------------------------

#[test]
fn decimal_round_trips_including_large_and_negative_values() {
    for text in ["0", "1", "5", "123456789012345678901234567890"] {
        let value = Fr::from_decimal(text).unwrap();
        assert_eq!(value.to_decimal(), text);
    }
    // Negative literals reduce into the field, as the IR's folded constants may.
    let minus_one = Fr::from_decimal("-1").unwrap();
    assert_eq!(minus_one.add(Fr::one()), Fr::zero());
    assert!(Fr::from_decimal("12x").is_err());
    assert!(Fr::from_decimal("").is_err());
}

#[test]
fn zero_has_no_inverse() {
    assert!(Fr::zero().inverse().is_none());
    let five = Fr::from_decimal("5").unwrap();
    assert_eq!(five.mul(five.inverse().unwrap()), Fr::one());
}

// --- IR validation -------------------------------------------------------

#[test]
fn valid_ir_loads() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    assert_eq!(ir.name, "IsZero");
    assert_eq!(ir.wire_count(), 9);
    assert_eq!(ir.advice_wires(), vec![(3, "inv")]);
}

#[test]
fn rejects_a_future_schema_version() {
    let text = ISZERO_IR.replace("\"schema_version\": 1", "\"schema_version\": 99");
    let message = Ir::from_json(&text).unwrap_err();
    assert!(message.contains("unsupported IR schema version"), "{message}");
}

#[test]
fn rejects_forward_references() {
    // A node that reads a wire defined later would break the solver, so the
    // topological-order invariant is checked, not assumed.
    let text = ISZERO_IR.replace(
        r#"{"wire": 4, "op": "mul", "args": [1, 3]}"#,
        r#"{"wire": 4, "op": "mul", "args": [1, 7]}"#,
    );
    let message = Ir::from_json(&text).unwrap_err();
    assert!(message.contains("topologically ordered"), "{message}");
}

#[test]
fn rejects_wrong_arity() {
    let text = ISZERO_IR.replace(
        r#"{"wire": 4, "op": "mul", "args": [1, 3]}"#,
        r#"{"wire": 4, "op": "mul", "args": [1]}"#,
    );
    let message = Ir::from_json(&text).unwrap_err();
    assert!(message.contains("expected 2"), "{message}");
}

#[test]
fn rejects_sparse_wire_numbering() {
    let text = ISZERO_IR.replace(r#""wire": 5, "op": "const""#, r#""wire": 50, "op": "const""#);
    assert!(Ir::from_json(&text).is_err());
}

// --- Lowering ------------------------------------------------------------

#[test]
fn linear_operations_cost_nothing() {
    // add/sub/neg/const fold into linear combinations, so the only constraint
    // is the assertion itself. This is the concrete reason the Core IR is not
    // shaped like R1CS: the cost model is a property of the *backend*.
    let ir = Ir::from_json(LINEAR_IR).unwrap();
    let r1cs = lower::<Fr>(&ir).unwrap();
    assert_eq!(r1cs.constraints.len(), 1);
    // Variables: constant one, plus the two inputs. No node allocated any.
    assert_eq!(r1cs.num_vars, 3);
}

#[test]
fn multiplications_and_hints_allocate_variables() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let r1cs = lower::<Fr>(&ir).unwrap();
    // one + x + out + inv(hint) + two multiplication results
    assert_eq!(r1cs.num_vars, 6);
    // two multiplications + two assertions
    assert_eq!(r1cs.constraints.len(), 4);
    // Exactly one public input, and it is `out`.
    assert_eq!(r1cs.public_vars.len(), 1);
}

#[test]
fn a_hint_adds_a_variable_but_no_constraint() {
    // The mechanical statement of "advice is unconstrained": removing the
    // hint's *constraint* is impossible, because there never was one.
    let ir = Ir::from_json(ISZERO_BROKEN_IR).unwrap();
    let r1cs = lower::<Fr>(&ir).unwrap();
    assert_eq!(r1cs.num_vars, 5); // one + x + out + inv + one multiplication
    assert_eq!(r1cs.constraints.len(), 2); // one multiplication + one assertion
}

#[test]
fn assertion_violations_report_the_source_line() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let (_, violated) = run(&ir, &[("x", "5"), ("out", "1")], &[]);
    assert!(
        violated.iter().any(|origin| origin.contains("line 17")),
        "expected the source-level origin, got {violated:?}"
    );
}

// --- Witness solving and the forgery -------------------------------------

#[test]
fn honest_witnesses_satisfy_the_correct_circuit() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    for (x, out) in [("0", "1"), ("5", "0"), ("123456789", "0")] {
        let (_, violated) = run(&ir, &[("x", x), ("out", out)], &[]);
        assert!(violated.is_empty(), "x={x} rejected: {violated:?}");
    }
}

#[test]
fn the_hint_computes_the_inverse_or_zero() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let (wires, _) = run(&ir, &[("x", "5"), ("out", "0")], &[]);
    let five = Fr::from_decimal("5").unwrap();
    assert_eq!(wires[3], five.inverse().unwrap());

    let (wires, _) = run(&ir, &[("x", "0"), ("out", "1")], &[]);
    assert_eq!(wires[3], Fr::zero(), "inv_or_zero(0) must be 0");
}

#[test]
fn the_correct_circuit_refuses_the_forgery() {
    // The prover ignores the hint and picks inv = (1 - out)/x = 0 to satisfy
    // assertion (1) while claiming out = 1. Assertion (2) catches it.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let (_, violated) = run(&ir, &[("x", "5"), ("out", "1")], &[("inv", "0")]);
    assert_eq!(violated.len(), 1);
    assert!(violated[0].contains("(x * out) == 0"), "{violated:?}");
}

#[test]
fn the_under_constrained_circuit_accepts_the_forgery() {
    // THE point of the whole phase: identical inputs, identical forged advice,
    // one missing assertion — and the constraint system is satisfied, so a
    // prover can produce a real proof of "5 == 0".
    let ir = Ir::from_json(ISZERO_BROKEN_IR).unwrap();
    let (_, violated) = run(&ir, &[("x", "5"), ("out", "1")], &[("inv", "0")]);
    assert!(violated.is_empty(), "expected the forgery to pass: {violated:?}");
}

#[test]
fn the_broken_circuit_also_accepts_honest_witnesses() {
    // Which is why the bug ships: honest testing never sees it.
    let ir = Ir::from_json(ISZERO_BROKEN_IR).unwrap();
    for (x, out) in [("0", "1"), ("5", "0")] {
        let (_, violated) = run(&ir, &[("x", x), ("out", out)], &[]);
        assert!(violated.is_empty(), "x={x}: {violated:?}");
    }
}

#[test]
fn missing_input_values_are_reported_by_name() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let given = inputs(&[("x", "5")]);
    let advice = HashMap::new();
    let error = solve::<Fr>(&ir, &SolveInputs { inputs: &given, advice_overrides: &advice })
        .unwrap_err();
    assert!(error.contains("'out'"), "{error}");
}
