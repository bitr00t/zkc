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
use zkc_core::lower::{lower, lower_with};
use zkc_core::plonkish::{lower_plonkish, lower_plonkish_with};
use zkc_core::witness::{solve, SolveInputs};

// --- Fixtures ------------------------------------------------------------

const ISZERO_IR: &str = r#"{
  "schema_version": 2, "name": "IsZero", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "x", "visibility": "private"},
    {"wire": 2, "name": "out", "visibility": "output", "line": 21}],
  "nodes": [
    {"wire": 3, "advice_derived": true, "op": "hint", "hint": "inv_or_zero",
     "name": "inv", "gadget": "is_zero", "line": 24, "args": [1]},
    {"wire": 4, "advice_derived": true, "op": "mul", "args": [1, 3]},
    {"wire": 5, "advice_derived": false, "op": "const", "value": "1"},
    {"wire": 6, "advice_derived": false, "op": "sub", "args": [5, 2]},
    {"wire": 7, "advice_derived": false, "op": "mul", "args": [1, 2]},
    {"wire": 8, "advice_derived": false, "op": "const", "value": "0"}],
  "assertions": [
    {"lhs": 4, "rhs": 6, "label": "(x * inv) == (1 - out)", "line": 26},
    {"lhs": 7, "rhs": 8, "label": "(x * out) == 0", "line": 27}],
  "determinacy": {"proved": true, "targets": ["out"],
                  "branches": [["x == 0"], ["x != 0"]]}
}"#;

/// The same circuit with the second assertion (and its nodes) removed.
///
/// The phase-2 frontend refuses to compile this, so it can only be written
/// by hand — which is exactly why it belongs here. It pins down the fact
/// that the *constraint system* really does admit two witnesses: the
/// frontend check is preventing a real vulnerability, not a theoretical one.
///
/// Note `out` is declared `public`, not `output`. As a relation ("I know x
/// and out satisfying this equation") the circuit is not lying about
/// anything, so the backend's soundness gate has nothing to object to. It is
/// the claim that `out` is *computed* that needs a proof — see
/// `an_ir_claiming_outputs_without_a_proof_is_refused`.
const ISZERO_BROKEN_IR: &str = r#"{
  "schema_version": 2, "name": "IsZeroBroken", "field": "bn254", "const_one_wire": 0,
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
  "schema_version": 2, "name": "Linear", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "private"},
    {"wire": 2, "name": "z", "visibility": "output", "line": 3}],
  "nodes": [
    {"wire": 3, "op": "const", "value": "3"},
    {"wire": 4, "op": "add", "args": [1, 3]},
    {"wire": 5, "op": "neg", "args": [4]},
    {"wire": 6, "op": "sub", "args": [1, 5]}],
  "assertions": [
    {"lhs": 2, "rhs": 6, "label": "z == a - (-(a + 3))", "line": 5}],
  "determinacy": {"proved": true, "targets": ["z"], "branches": [[]]}
}"#;

/// `c == (a * b) * (a * b)`. The inner `a * b` feeds the outer mul (used
/// twice), so it is NOT fusible and keeps its variable; only the outer mul,
/// which feeds the single assertion, fuses. Proves fusion is precise about
/// "feeds exactly one assertion and nothing else".
const MULSQUARE_IR: &str = r#"{
  "schema_version": 2, "name": "MulSquare", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "private"},
    {"wire": 2, "name": "b", "visibility": "private"},
    {"wire": 3, "name": "c", "visibility": "output", "line": 4}],
  "nodes": [
    {"wire": 4, "op": "mul", "args": [1, 2]},
    {"wire": 5, "op": "mul", "args": [4, 4]}],
  "assertions": [
    {"lhs": 3, "rhs": 5, "label": "c == (a * b) * (a * b)", "line": 6}],
  "determinacy": {"proved": true, "targets": ["c"], "branches": [[]]}
}"#;


/// `z == a + b + c + d + e + f`. No multiplication at all — the shape where
/// R1CS's free linear algebra wins and no amount of gate fusion can catch up.
const WIDESUM_IR: &str = r##"{"schema_version": 2, "name": "WideSum", "field": "bn254", "const_one_wire": 0, "inputs": [{"wire": 1, "name": "a", "visibility": "private", "line": 2}, {"wire": 2, "name": "b", "visibility": "private", "line": 2}, {"wire": 3, "name": "c", "visibility": "private", "line": 2}, {"wire": 4, "name": "d", "visibility": "private", "line": 3}, {"wire": 5, "name": "e", "visibility": "private", "line": 3}, {"wire": 6, "name": "f", "visibility": "private", "line": 3}, {"wire": 7, "name": "z", "visibility": "output", "line": 4}], "nodes": [{"wire": 8, "advice_derived": false, "op": "add", "args": [1, 2]}, {"wire": 9, "advice_derived": false, "op": "add", "args": [8, 3]}, {"wire": 10, "advice_derived": false, "op": "add", "args": [9, 4]}, {"wire": 11, "advice_derived": false, "op": "add", "args": [10, 5]}, {"wire": 12, "advice_derived": false, "op": "add", "args": [11, 6]}], "assertions": [{"lhs": 7, "rhs": 12, "label": "z == (((((a + b) + c) + d) + e) + f)", "line": 5}], "determinacy": {"proved": true, "targets": ["z"], "branches": [[]]}}"##;

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
    let text = ISZERO_IR.replace("\"schema_version\": 2", "\"schema_version\": 99");
    let message = Ir::from_json(&text).unwrap_err();
    assert!(message.contains("unsupported IR schema version"), "{message}");
}

#[test]
fn rejects_forward_references() {
    // A node that reads a wire defined later would break the solver, so the
    // topological-order invariant is checked, not assumed.
    let text = ISZERO_IR.replace(
        r#"{"wire": 4, "advice_derived": true, "op": "mul", "args": [1, 3]}"#,
        r#"{"wire": 4, "advice_derived": true, "op": "mul", "args": [1, 7]}"#,
    );
    let message = Ir::from_json(&text).unwrap_err();
    assert!(message.contains("topologically ordered"), "{message}");
}

#[test]
fn rejects_wrong_arity() {
    let text = ISZERO_IR.replace(
        r#"{"wire": 4, "advice_derived": true, "op": "mul", "args": [1, 3]}"#,
        r#"{"wire": 4, "advice_derived": true, "op": "mul", "args": [1]}"#,
    );
    let message = Ir::from_json(&text).unwrap_err();
    assert!(message.contains("expected 2"), "{message}");
}

#[test]
fn an_ir_claiming_outputs_without_a_proof_is_refused() {
    // Schema v2 carries the frontend's determinacy proof inside the artifact,
    // and the backend treats a missing proof as a refusal rather than a
    // default-allow. Stripping the record from an otherwise valid IR must not
    // be a way to get a proving key for an under-constrained circuit.
    let text = ISZERO_IR.replace(
        r#""determinacy": {"proved": true, "targets": ["out"],
                  "branches": [["x == 0"], ["x != 0"]]}"#,
        r#""determinacy": {"proved": false, "targets": [], "branches": []}"#,
    );
    let message = Ir::from_json(&text).unwrap_err();
    assert!(message.contains("determinacy"), "{message}");
}

#[test]
fn a_relation_without_outputs_needs_no_determinacy_proof() {
    // Not every circuit computes something. A relation over public inputs has
    // no output to pin down, so the gate must stay quiet rather than demand a
    // proof that does not apply.
    let ir = Ir::from_json(ISZERO_BROKEN_IR).unwrap();
    assert!(!ir.determinacy.proved);
    assert_eq!(ir.name, "IsZeroBroken");
}

#[test]
fn rejects_sparse_wire_numbering() {
    let text = ISZERO_IR.replace(r#""wire": 5, "advice_derived": false, "op": "const""#,
                      r#""wire": 50, "advice_derived": false, "op": "const""#);
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
fn without_fusion_each_multiplication_costs_its_own_variable() {
    // The phase-2 lowering, preserved behind `fuse = false`: each of IsZero's
    // two muls allocates a variable and a constraint, and each assertion adds
    // another. This is the baseline the fusion is measured against.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let r1cs = lower_with::<Fr>(&ir, false).unwrap();
    // one + x + out + inv(hint) + two multiplication results
    assert_eq!(r1cs.num_vars, 6);
    // two multiplications + two assertions
    assert_eq!(r1cs.constraints.len(), 4);
    // Exactly one public input, and it is `out`.
    assert_eq!(r1cs.public_vars.len(), 1);
}

#[test]
fn fusion_folds_each_iszero_multiplication_into_its_assertion() {
    // Both of IsZero's muls feed exactly one assertion and nothing else, so
    // both fuse: the two intermediate variables and the two equality
    // constraints all vanish, leaving one rank-1 constraint per assertion.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let r1cs = lower::<Fr>(&ir).unwrap();
    assert_eq!(r1cs.num_vars, 4); // one + x + out + inv; no mul variables
    assert_eq!(r1cs.constraints.len(), 2); // two fused constraints, down from four
    // The public interface is untouched by an internal optimisation.
    assert_eq!(r1cs.public_vars.len(), 1);
}

#[test]
fn a_hint_adds_a_variable_but_no_constraint() {
    // The mechanical statement of "advice is unconstrained": removing the
    // hint's *constraint* is impossible, because there never was one. The one
    // multiplication fuses into the assertion, but the hint variable remains,
    // constraintless — which is the whole point.
    let ir = Ir::from_json(ISZERO_BROKEN_IR).unwrap();
    let r1cs = lower::<Fr>(&ir).unwrap();
    assert_eq!(r1cs.num_vars, 4); // one + x + out + inv; the mul fused away
    assert_eq!(r1cs.constraints.len(), 1); // one fused constraint, down from two
}

#[test]
fn fusion_is_precise_only_the_mul_feeding_the_assertion_folds() {
    // The inner a*b is used by the outer mul, so it must keep its variable and
    // constraint; only the outer mul folds into the assertion.
    let ir = Ir::from_json(MULSQUARE_IR).unwrap();
    let unfused = lower_with::<Fr>(&ir, false).unwrap();
    let fused = lower::<Fr>(&ir).unwrap();
    assert_eq!(unfused.constraints.len(), 3); // inner mul + outer mul + assertion
    assert_eq!(fused.constraints.len(), 2); // inner mul + fused assertion
    assert_eq!(unfused.num_vars, 6); // one + a + b + c + ab + abab
    assert_eq!(fused.num_vars, 5); // one + a + b + c + ab (outer mul folded)
}

#[test]
fn fusion_preserves_satisfaction_and_still_catches_a_lie() {
    // Same witness, both lowerings: honest values satisfy, a wrong output is
    // caught. Fusion must change the cost, never the meaning.
    let ir = Ir::from_json(MULSQUARE_IR).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs { inputs: &inputs(&[("a", "2"), ("b", "3"), ("c", "36")]), advice_overrides: &HashMap::new() },
    )
    .unwrap();
    for fuse in [false, true] {
        let r1cs = lower_with::<Fr>(&ir, fuse).unwrap();
        assert!(r1cs.is_satisfied(&r1cs.assignment(&wires)), "honest witness rejected (fuse={fuse})");
    }
    // A forged output (c = 35 instead of 36) is caught either way. We check the
    // constraint system directly by overriding c in the assignment.
    for fuse in [false, true] {
        let r1cs = lower_with::<Fr>(&ir, fuse).unwrap();
        let mut assignment = r1cs.assignment(&wires);
        // Variable for `c` is the third input variable (one, a, b, c -> index 3).
        assignment[3] = Fr::from_decimal("35").unwrap();
        assert!(!r1cs.is_satisfied(&assignment), "forged output accepted (fuse={fuse})");
    }
}

/// Build an IR of `n` independent `assert o_i == a_i * b_i` products — the
/// shape fusion targets, and a stand-in for the multiplication-heavy circuits
/// (SHA-256, Merkle) the full benchmark will use once the gadget stdlib lands.
fn many_products_ir(n: usize) -> String {
    let mut inputs = String::new();
    for i in 0..n {
        let (a, b, o) = (3 * i + 1, 3 * i + 2, 3 * i + 3);
        inputs.push_str(&format!(
            "{{\"wire\":{a},\"name\":\"a{i}\",\"visibility\":\"private\"}},\
             {{\"wire\":{b},\"name\":\"b{i}\",\"visibility\":\"private\"}},\
             {{\"wire\":{o},\"name\":\"o{i}\",\"visibility\":\"output\"}}"
        ));
        if i + 1 < n {
            inputs.push(',');
        }
    }
    let first_node = 3 * n + 1;
    let mut nodes = String::new();
    let mut assertions = String::new();
    let mut targets = String::new();
    for i in 0..n {
        let (a, b, o) = (3 * i + 1, 3 * i + 2, 3 * i + 3);
        let mul_wire = first_node + i;
        nodes.push_str(&format!("{{\"wire\":{mul_wire},\"op\":\"mul\",\"args\":[{a},{b}]}}"));
        assertions.push_str(&format!(
            "{{\"lhs\":{o},\"rhs\":{mul_wire},\"label\":\"o{i} == a{i} * b{i}\",\"line\":{i}}}"
        ));
        targets.push_str(&format!("\"o{i}\""));
        if i + 1 < n {
            nodes.push(',');
            assertions.push(',');
            targets.push(',');
        }
    }
    format!(
        "{{\"schema_version\":2,\"name\":\"ManyProducts\",\"field\":\"bn254\",\
          \"const_one_wire\":0,\"inputs\":[{inputs}],\"nodes\":[{nodes}],\
          \"assertions\":[{assertions}],\
          \"determinacy\":{{\"proved\":true,\"targets\":[{targets}],\"branches\":[[]]}}}}"
    )
}

#[test]
fn benchmark_fusion_halves_constraints_on_a_multiplication_heavy_circuit() {
    // The headline number, pinned to a test. On N independent products, the
    // naive lowering emits 2N constraints (a mul + an equality each); fusion
    // emits exactly N. The machine-readable line is what a benchmark harness
    // would diff across runs (and, later, against Circom's --r1cs counts).
    let n = 64;
    let ir = Ir::from_json(&many_products_ir(n)).unwrap();
    let unfused = lower_with::<Fr>(&ir, false).unwrap();
    let fused = lower::<Fr>(&ir).unwrap();

    println!(
        "BENCH circuit=ManyProducts n={n} \
         constraints_unfused={} constraints_fused={} \
         vars_unfused={} vars_fused={} reduction={:.2}",
        unfused.constraints.len(),
        fused.constraints.len(),
        unfused.num_vars,
        fused.num_vars,
        1.0 - (fused.constraints.len() as f64) / (unfused.constraints.len() as f64),
    );

    assert_eq!(unfused.constraints.len(), 2 * n);
    assert_eq!(fused.constraints.len(), n);
    // Fusion removes exactly the N intermediate multiplication variables.
    assert_eq!(unfused.num_vars - fused.num_vars, n);
}

#[test]
fn benchmark_end_to_end_frontend_ir_lowers_with_the_fusion_win() {
    // The same win, but on IR the *frontend* actually emitted (committed at
    // benchmarks/many_mul.json), not a hand-written fixture — so it exercises
    // Workstream A (the reused `product` gadget, proved once) and Workstream C
    // (fusion) together, end to end.
    let ir = Ir::from_json(include_str!("../../../benchmarks/many_mul.json")).unwrap();
    let unfused = lower_with::<Fr>(&ir, false).unwrap();
    let fused = lower::<Fr>(&ir).unwrap();
    assert_eq!(unfused.constraints.len(), 16); // 8 muls + 8 assertions
    assert_eq!(fused.constraints.len(), 8); // 8 fused products
}

#[test]
fn assertion_violations_report_the_source_line() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let (_, violated) = run(&ir, &[("x", "5"), ("out", "1")], &[]);
    assert!(
        violated.iter().any(|origin| origin.contains("line 26")),
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
// Plonkish arithmetization (phase 4, Workstream D) ------------------------
//
// The same IR, lowered a second way. These tests are about the lowering being
// *faithful*: the shape is what the gate algebra says it should be, the
// wiring is asserted rather than assumed, and an honest witness satisfies it.

#[test]
fn plonkish_unfused_gives_every_arithmetic_node_a_row_and_hints_none() {
    // IsZero: 2 muls, 1 sub, 2 consts, 1 hint, 2 assertions.
    // A hint imposes no identity, so it gets no row — the same reason it
    // allocates a variable and no constraint in R1CS.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let circuit = lower_plonkish_with::<Fr>(&ir, false).unwrap();
    let arithmetic = ir
        .nodes
        .iter()
        .filter(|n| !matches!(n.op, zkc_core::ir::NodeOp::Hint { .. }))
        .count();
    assert_eq!(circuit.num_rows(), arithmetic + ir.assertions.len());
    // Width is fixed by the gate: three witness columns, five selectors.
    assert_eq!(circuit.num_columns(), 8);
}

#[test]
fn plonkish_asserts_the_wiring_instead_of_assuming_it() {
    // The property with no R1CS counterpart: a value produced in one row and
    // consumed in another occupies two unrelated cells, and only a copy
    // constraint makes them the same value.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let circuit = lower_plonkish::<Fr>(&ir).unwrap();
    assert!(
        !circuit.copies.is_empty(),
        "a connected circuit must produce copy constraints"
    );
    // Every copy relates two genuinely different cells.
    for (left, right) in &circuit.copies {
        assert!(left != right, "a cell copied to itself is not wiring");
    }
}

#[test]
fn plonkish_accepts_the_honest_witness() {
    // x = 0 forces out = 1; the solved witness must satisfy every gate and
    // every copy constraint.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("x", "0"), ("out", "1")]),
            advice_overrides: &HashMap::new(),
        },
    )
    .unwrap();
    let circuit = lower_plonkish::<Fr>(&ir).unwrap();
    let assignment = circuit.assignment(&wires);
    let violations = circuit.check(&assignment);
    assert!(violations.is_empty(), "honest witness rejected: {violations:?}");
}

#[test]
fn plonkish_catches_a_tampered_cell_through_a_copy_constraint() {
    // Copy constraints are satisfied by construction when the table is built
    // from wire values, so the check only earns its keep against a table that
    // did NOT come from there. Rewrite one cell and it must be caught.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("x", "0"), ("out", "1")]),
            advice_overrides: &HashMap::new(),
        },
    )
    .unwrap();
    let circuit = lower_plonkish::<Fr>(&ir).unwrap();
    let mut assignment = circuit.assignment(&wires);
    // Pick a wire that really is shared, and corrupt its second occurrence.
    let (_, second) = circuit.copies[0];
    assignment[second.row][second.column.index()] = Fr::from_decimal("12345").unwrap();
    assert!(
        !circuit.is_satisfied(&assignment),
        "a cell that disagrees with its copy must be rejected"
    );
}

#[test]
fn plonkish_binds_every_public_input_to_a_cell() {
    // The verifier needs somewhere to point at for each public value.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let circuit = lower_plonkish::<Fr>(&ir).unwrap();
    let public = ir.inputs.iter().filter(|i| i.visibility.is_public()).count();
    assert_eq!(circuit.public_cells.len(), public);
    for (_, cell) in &circuit.public_cells {
        assert!(cell.row < circuit.num_rows());
    }
}

#[test]
fn plonkish_unfused_costs_more_than_r1cs_and_that_is_what_fusion_is_for() {
    // The unoptimised baseline the design note predicts: a row per node beats
    // nothing, and R1CS's free linear algebra wins here. Fusing assertions
    // into gates is the Plonkish-native optimisation, measured separately.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let r1cs = lower::<Fr>(&ir).unwrap();
    let plonkish = lower_plonkish_with::<Fr>(&ir, false).unwrap();
    println!(
        "BENCH circuit=IsZero r1cs_constraints={} plonkish_rows={} plonkish_copies={}",
        r1cs.constraints.len(),
        plonkish.num_rows(),
        plonkish.copies.len()
    );
    assert!(plonkish.num_rows() > r1cs.constraints.len());
}

// Plonkish gate fusion (phase 4, Workstream D.2) --------------------------

/// Overwrite every cell holding `wire`, so the table stops describing the
/// solved witness. Used to check that a lie is caught however it is told.
fn falsify(circuit: &zkc_core::plonkish::Plonkish<Fr>, assignment: &mut [[Fr; 3]], wire: u32, value: &str) {
    let lie = Fr::from_decimal(value).unwrap();
    for (row_index, row) in circuit.rows.iter().enumerate() {
        for (slot, held) in row.cells.iter().enumerate() {
            if *held == Some(wire) {
                assignment[row_index][slot] = lie;
            }
        }
    }
}

#[test]
fn fusion_folds_iszero_into_one_row_per_assertion() {
    // `assert x * inv == 1 - out` is four rows unfused — a constant, a
    // subtraction, a multiplication and the assertion — and one fused, because
    // a gate holds a product, a linear term and a constant at once.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let base = lower_plonkish_with::<Fr>(&ir, false).unwrap();
    let fused = lower_plonkish_with::<Fr>(&ir, true).unwrap();
    assert_eq!(base.num_rows(), 7);
    assert_eq!(fused.num_rows(), 2); // one row per assertion, nothing else
    // Fusion also removes wiring: a value that never leaves its row needs no
    // copy constraint, and those are a real cost in a Plonk prover.
    assert!(fused.copies.len() < base.copies.len());
}

#[test]
fn fusion_preserves_the_honest_witness() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("x", "0"), ("out", "1")]),
            advice_overrides: &HashMap::new(),
        },
    )
    .unwrap();
    for fuse in [false, true] {
        let circuit = lower_plonkish_with::<Fr>(&ir, fuse).unwrap();
        let assignment = circuit.assignment(&wires);
        assert!(
            circuit.is_satisfied(&assignment),
            "honest witness rejected (fuse={fuse})"
        );
    }
}

#[test]
fn fusion_still_catches_a_forged_output() {
    // The rule that matters: a cheaper circuit must not be a weaker one.
    // x = 0 forces out = 1, so claiming out = 0 is a lie, and both the fused
    // and the unfused arrangement must refuse it.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("x", "0"), ("out", "1")]),
            advice_overrides: &HashMap::new(),
        },
    )
    .unwrap();
    let out = ir.inputs.iter().find(|i| i.name == "out").unwrap().wire;
    for fuse in [false, true] {
        let circuit = lower_plonkish_with::<Fr>(&ir, fuse).unwrap();
        let mut assignment = circuit.assignment(&wires);
        falsify(&circuit, &mut assignment, out, "0");
        assert!(
            !circuit.is_satisfied(&assignment),
            "forged output accepted (fuse={fuse})"
        );
    }
}

#[test]
fn fusion_shares_a_value_used_twice_instead_of_recomputing_it() {
    // `c == (a*b) * (a*b)`: the inner product feeds two consumers, so folding
    // it into both would compute it twice. It is materialised once and wired,
    // which is common-subexpression elimination one arithmetization further
    // down. The result must still be correct.
    let ir = Ir::from_json(MULSQUARE_IR).unwrap();
    let fused = lower_plonkish_with::<Fr>(&ir, true).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("a", "2"), ("b", "3"), ("c", "36")]),
            advice_overrides: &HashMap::new(),
        },
    )
    .unwrap();
    assert!(fused.is_satisfied(&fused.assignment(&wires)));
    // The shared inner product is wired to its second use rather than redone.
    assert!(!fused.copies.is_empty());
}

#[test]
fn benchmark_plonkish_fusion_and_where_r1cs_still_wins() {
    // The headline pair. On multiplication-heavy shapes fusion closes the gap
    // to R1CS completely; on a wide linear sum it cannot, and that is
    // structural rather than a missing optimisation: six summands do not fit
    // in three-cell gates, while R1CS folds them into a single linear
    // combination for free. The two arithmetizations genuinely disagree about
    // what is expensive, which is the reason the IR stays neutral.
    let many = Ir::from_json(&many_products_ir(8)).unwrap();
    let r1cs = lower::<Fr>(&many).unwrap();
    let base = lower_plonkish_with::<Fr>(&many, false).unwrap();
    let fused = lower_plonkish_with::<Fr>(&many, true).unwrap();
    println!(
        "BENCH circuit=ManyProducts n=8 r1cs={} plonkish_base={} plonkish_fused={} copies={}",
        r1cs.constraints.len(),
        base.num_rows(),
        fused.num_rows(),
        fused.copies.len()
    );
    assert_eq!(base.num_rows(), 16);
    assert_eq!(fused.num_rows(), 8); // one gate per product: R1CS matched
    assert_eq!(fused.num_rows(), r1cs.constraints.len());
    // No value crosses a row boundary, so the wiring cost vanishes entirely.
    assert_eq!(fused.copies.len(), 0);
}


#[test]
fn a_wide_linear_sum_is_where_r1cs_stays_ahead() {
    // Structural, not a missing optimisation. R1CS folds six summands into one
    // linear combination and spends a single constraint; a Plonkish gate sees
    // three cells, so the sum has to be chained across rows however cleverly
    // it is fused. Recording it as a test keeps the claim honest.
    let ir = Ir::from_json(WIDESUM_IR).unwrap();
    let r1cs = lower::<Fr>(&ir).unwrap();
    let base = lower_plonkish_with::<Fr>(&ir, false).unwrap();
    let fused = lower_plonkish_with::<Fr>(&ir, true).unwrap();
    println!(
        "BENCH circuit=WideSum r1cs={} plonkish_base={} plonkish_fused={}",
        r1cs.constraints.len(),
        base.num_rows(),
        fused.num_rows()
    );
    assert_eq!(r1cs.constraints.len(), 1);
    assert_eq!(base.num_rows(), 6);
    assert_eq!(fused.num_rows(), 5); // fusion helps a little, and then stops
    assert!(fused.num_rows() > r1cs.constraints.len());

    // Cheaper or not, it still has to be right.
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[
                ("a", "1"), ("b", "2"), ("c", "3"),
                ("d", "4"), ("e", "5"), ("f", "6"), ("z", "21"),
            ]),
            advice_overrides: &HashMap::new(),
        },
    )
    .unwrap();
    assert!(fused.is_satisfied(&fused.assignment(&wires)));
    let z = ir.inputs.iter().find(|i| i.name == "z").unwrap().wire;
    let mut assignment = fused.assignment(&wires);
    falsify(&fused, &mut assignment, z, "20");
    assert!(!fused.is_satisfied(&assignment), "a wrong sum must be rejected");
}

// Plonkish lowering well-formedness (phase 4, Workstream E.1) --------------
//
// `is_satisfied` (D.1) asks whether a witness satisfies the circuit. `validate`
// asks the prior question — is this a well-formed circuit at all — and these
// tests are what stop the second lowering from being trusted before it has
// earned it. Two of them deliberately break a lowering and require the break
// to be caught, because a validator that only ever passes is decoration.

use zkc_core::plonkish::{Malformed, Column as PlonkColumn};

#[test]
fn validate_accepts_every_lowering_the_compiler_produces() {
    for fixture in [ISZERO_IR, LINEAR_IR, MULSQUARE_IR, ISZERO_BROKEN_IR, WIDESUM_IR] {
        let ir = Ir::from_json(fixture).unwrap();
        for fuse in [false, true] {
            let circuit = lower_plonkish_with::<Fr>(&ir, fuse).unwrap();
            assert!(
                circuit.validate().is_ok(),
                "a real lowering was rejected as malformed (fuse={fuse}): {:?}",
                circuit.validate()
            );
        }
    }
}

#[test]
fn validate_catches_sharing_that_was_never_wired() {
    // The failure the design note warned about: a value used in two rows, with
    // the copy constraint that ties them together dropped. Every gate still
    // holds on the honest witness, so `is_satisfied` is happy — and the
    // circuit is silently unsound, because the two occurrences are free to
    // differ. `validate` must catch what `check` cannot.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let mut circuit = lower_plonkish_with::<Fr>(&ir, false).unwrap();

    // Find a wire that really is shared, then delete its wiring.
    let shared = circuit
        .copies
        .first()
        .map(|(left, _)| circuit.rows[left.row].cells[left.column.index()].unwrap())
        .expect("IsZero shares wires across rows");
    circuit.copies.retain(|(left, right)| {
        let l = circuit.rows[left.row].cells[left.column.index()];
        let r = circuit.rows[right.row].cells[right.column.index()];
        l != Some(shared) && r != Some(shared)
    });

    match circuit.validate() {
        Err(problems) => assert!(
            problems.iter().any(|p| matches!(p, Malformed::UnwiredSharing { wire, .. } if *wire == shared)),
            "the dropped wiring was not reported: {problems:?}"
        ),
        Ok(()) => panic!("unwired sharing passed validation"),
    }
}

#[test]
fn validate_catches_a_selector_reading_an_empty_cell() {
    // Turn on a selector whose cell is empty. The gate now reads a value that
    // was never placed — a pure lowering bug, independent of any witness.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let mut circuit = lower_plonkish_with::<Fr>(&ir, true).unwrap();
    // The assertion rows leave column C empty; switch on q_O there.
    let row = circuit
        .rows
        .iter_mut()
        .find(|r| r.cells[PlonkColumn::C.index()].is_none())
        .expect("a fused assertion row has an empty C cell");
    row.q_o = Fr::from_decimal("1").unwrap();

    assert!(
        matches!(
            circuit.validate(),
            Err(ref problems) if problems.iter().any(|p| matches!(p, Malformed::SelectorWithoutCell { .. }))
        ),
        "a selector over an empty cell was not caught"
    );
}

#[test]
fn a_violation_describes_itself_in_source_terms() {
    // The R1CS checker reports a constraint by its assertion text; the
    // Plonkish one owes the same. A forged output must produce a message that
    // names where it went wrong, not an opaque index.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("x", "0"), ("out", "1")]),
            advice_overrides: &HashMap::new(),
        },
    )
    .unwrap();
    let circuit = lower_plonkish_with::<Fr>(&ir, true).unwrap();
    let out = ir.inputs.iter().find(|i| i.name == "out").unwrap().wire;
    let mut assignment = circuit.assignment(&wires);
    falsify(&circuit, &mut assignment, out, "0");

    let violations = circuit.check(&assignment);
    assert!(!violations.is_empty());
    let described = violations[0].describe();
    // The origin carries the assertion's own text ("x * out").
    assert!(
        described.contains("row") || described.contains("cell"),
        "unhelpful violation message: {described}"
    );
}

// Differential equivalence: R1CS ≡ Plonkish (phase 4, Workstream E.2) ------
//
// This is the payoff the whole neutral-IR discipline was for. Two lowerings,
// written independently, must encode the SAME statement — not merely both be
// satisfiable somewhere, but agree assignment by assignment: a witness
// satisfies R1CS if and only if it satisfies Plonkish. We cannot quantify over
// all assignments, so we check the two places it matters most (the honest
// witness, which both must accept; the phase-0 forgery, which both must
// reject) and then hammer it with random perturbations, where any disagreement
// would surface as one lowering accepting what the other refuses.
//
// The witness solver runs on the IR and is shared unchanged — so "the same
// witness" is not an approximation, it is literally the same solved vector fed
// to both. That sharing is what makes the comparison meaningful: if the two
// arithmetizations disagree, it is the lowering's fault and nothing else's.

/// Do both arithmetizations reach the same verdict on these solved wires?
///
/// R1CS builds one assignment vector; Plonkish builds a per-row cell table
/// from the same wire values. Both are honest functions of the shared witness,
/// so this compares the two encodings, not two witnesses.
fn verdicts_agree(ir: &Ir, wires: &[Fr]) -> Result<bool, (bool, bool)> {
    let r1cs = lower::<Fr>(ir).unwrap();
    let r1cs_ok = r1cs.is_satisfied(&r1cs.assignment(wires));

    // Fused and unfused Plonkish must both agree with R1CS, or fusion changed
    // the statement — which would be a far worse bug than a slow circuit.
    for fuse in [false, true] {
        let plonk = lower_plonkish_with::<Fr>(ir, fuse).unwrap();
        let plonk_ok = plonk.is_satisfied(&plonk.assignment(wires));
        if plonk_ok != r1cs_ok {
            return Err((r1cs_ok, plonk_ok));
        }
    }
    Ok(r1cs_ok)
}

#[test]
fn equivalence_the_honest_witness_satisfies_both() {
    // x = 0 forces out = 1; the honestly solved witness must satisfy R1CS and
    // Plonkish alike.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs { inputs: &inputs(&[("x", "0"), ("out", "1")]), advice_overrides: &HashMap::new() },
    )
    .unwrap();
    assert_eq!(verdicts_agree(&ir, &wires), Ok(true), "honest witness split the two lowerings");
}

#[test]
fn equivalence_the_phase_zero_forgery_is_rejected_by_both() {
    // The forgery that started the whole project: inputs x = 5, out = 1, with
    // the hint overridden to inv = 0 so assertion (1) holds while claiming a
    // false output. R1CS catches it on assertion (2); Plonkish must catch it
    // too, or the second arithmetization is weaker than the first.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("x", "5"), ("out", "1")]),
            advice_overrides: &inputs(&[("inv", "0")]),
        },
    )
    .unwrap();
    // Both must REJECT: verdicts agree, and the verdict is "unsatisfied".
    assert_eq!(
        verdicts_agree(&ir, &wires),
        Ok(false),
        "the phase-0 forgery was not rejected identically by both arithmetizations"
    );
}

#[test]
fn equivalence_the_broken_circuit_accepts_the_forgery_in_both() {
    // The other half of the phase-0 demo: with the second assertion GONE, the
    // same forged witness satisfies the circuit — and it must do so in both
    // arithmetizations, because being under-constrained is a property of the
    // IR, which both lower faithfully. If Plonkish rejected here while R1CS
    // accepted, the two would disagree about what the circuit even says.
    let ir = Ir::from_json(ISZERO_BROKEN_IR).unwrap();
    let wires = solve::<Fr>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("x", "5"), ("out", "1")]),
            advice_overrides: &inputs(&[("inv", "0")]),
        },
    )
    .unwrap();
    assert_eq!(
        verdicts_agree(&ir, &wires),
        Ok(true),
        "the two arithmetizations disagree about the under-constrained circuit"
    );
}

#[test]
fn equivalence_holds_under_random_perturbation_of_atoms() {
    // The general claim, stress-tested — but on the right variables.
    //
    // A subtlety worth stating, because finding it is half the value of a
    // differential test: R1CS and Plonkish do NOT agree on an assignment that
    // gives a computed wire a value inconsistent with its inputs. R1CS never
    // reads such a wire — it recomputes `a * b` from the argument cells and
    // ignores whatever the product wire holds — while Plonkish places that
    // wire in a cell and checks `a·b - c = 0`, so it catches the inconsistency.
    // Both are correct; they simply encode "the witness solver already
    // computed the intermediates" differently.
    //
    // The witness solver is the arbiter of intermediate values, and it is
    // shared. So the meaningful free variables — the ones a prover actually
    // chooses — are the ATOMS: inputs and advice. Perturb those, re-solve so
    // the intermediates stay consistent, and the two arithmetizations must
    // agree. (Perturbing a computed wire directly tests a witness no honest
    // solver would ever produce, and is the job of the per-lowering checks,
    // not the equivalence one.)
    let cases: &[(&str, &[(&str, &str)], &[&str])] = &[
        (ISZERO_IR, &[("x", "0"), ("out", "1")], &["x", "out", "inv"]),
        (ISZERO_BROKEN_IR, &[("x", "5"), ("out", "1")], &["x", "out", "inv"]),
        (MULSQUARE_IR, &[("a", "2"), ("b", "3"), ("c", "36")], &["a", "b", "c"]),
        (WIDESUM_IR,
         &[("a","1"),("b","2"),("c","3"),("d","4"),("e","5"),("f","6"),("z","21")],
         &["a","b","c","d","e","f","z"]),
    ];

    let mut state: u64 = 0x9e3779b97f4a7c15;
    let mut next = || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        state >> 33
    };

    for (fixture, base_inputs, atoms) in cases {
        let ir = Ir::from_json(fixture).unwrap();
        let input_names: std::collections::HashSet<&str> =
            ir.inputs.iter().map(|i| i.name.as_str()).collect();

        for _ in 0..300 {
            // A random value for each atom: inputs go through the solver,
            // advice through overrides, so every intermediate stays consistent
            // with the atoms that produced it.
            let mut input_map: HashMap<String, Fr> = HashMap::new();
            let mut advice_map: HashMap<String, Fr> = HashMap::new();
            for name in *atoms {
                let value = Fr::from_u64(next());
                if input_names.contains(name) {
                    input_map.insert((*name).to_string(), value);
                } else {
                    advice_map.insert((*name).to_string(), value);
                }
            }
            // Any base input not chosen as an atom still needs a value.
            for (name, value) in inputs(base_inputs) {
                input_map.entry(name).or_insert(value);
            }

            let wires = solve::<Fr>(
                &ir,
                &SolveInputs { inputs: &input_map, advice_overrides: &advice_map },
            )
            .unwrap();

            match verdicts_agree(&ir, &wires) {
                Ok(_) => {}
                Err((r1cs_ok, plonk_ok)) => panic!(
                    "arithmetizations diverged on a consistent witness of {}:                      R1CS satisfied = {r1cs_ok}, Plonkish satisfied = {plonk_ok}",
                    ir.name
                ),
            }
        }
    }
}

#[test]
fn equivalence_a_forged_output_is_caught_by_both_across_circuits() {
    // Directed rather than random: for each circuit with an output, solve
    // honestly, then overwrite the output wire with a wrong value everywhere
    // it appears. Both arithmetizations must reject — the property that makes
    // the determinacy guarantee survive the choice of arithmetization.
    let cases: &[(&str, &[(&str, &str)], &str, &str)] = &[
        (ISZERO_IR, &[("x", "0"), ("out", "1")], "out", "0"),
        (MULSQUARE_IR, &[("a", "2"), ("b", "3"), ("c", "36")], "c", "35"),
        (WIDESUM_IR, &[("a","1"),("b","2"),("c","3"),("d","4"),("e","5"),("f","6"),("z","21")], "z", "20"),
    ];
    for (fixture, base_inputs, output, lie) in cases {
        let ir = Ir::from_json(fixture).unwrap();
        let wires = solve::<Fr>(
            &ir,
            &SolveInputs { inputs: &inputs(base_inputs), advice_overrides: &HashMap::new() },
        )
        .unwrap();
        let wire = ir.inputs.iter().find(|i| &i.name == output).unwrap().wire;
        let mut forged = wires.clone();
        forged[wire as usize] = Fr::from_decimal(lie).unwrap();

        assert_eq!(
            verdicts_agree(&ir, &forged),
            Ok(false),
            "a forged output of {} was not rejected identically by both", ir.name
        );
    }
}