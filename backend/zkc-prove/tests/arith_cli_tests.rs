//! End-to-end tests for the `--arith` path (phase 4, Workstream F.2).
//!
//! These drive the built `zkc-prove` binary the way a user does: on an IR file
//! and an inputs file, with each arithmetization. The claim under test is the
//! one F.2 exists to make good — a circuit can be *built* either way, and the
//! determinacy record is the same on both paths because soundness lives in the
//! IR, not in the arithmetization.

use std::io::Write;
use std::process::Command;

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_zkc-prove")
}

/// Write text to a uniquely named temp file and return its path.
fn temp(name: &str, contents: &str) -> std::path::PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("zkc_f2_{}_{}", std::process::id(), name));
    let mut file = std::fs::File::create(&path).unwrap();
    file.write_all(contents.as_bytes()).unwrap();
    path
}

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

const HONEST: &str = r#"{ "inputs": { "x": "0", "out": "1" } }"#;
const FORGED: &str = r#"{ "inputs": { "x": "5", "out": "1" }, "advice": { "inv": "0" } }"#;

fn run(ir: &std::path::Path, inputs: &std::path::Path, arith: &str) -> (bool, String) {
    let output = Command::new(bin())
        .args(["--ir", ir.to_str().unwrap(), "--inputs", inputs.to_str().unwrap(), "--arith", arith])
        .output()
        .expect("failed to run zkc-prove");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (output.status.success(), text)
}

#[test]
fn r1cs_path_proves_the_honest_witness() {
    let ir = temp("iszero.ir.json", ISZERO_IR);
    let inputs = temp("honest.json", HONEST);
    let (ok, text) = run(&ir, &inputs, "r1cs");
    assert!(ok, "honest R1CS run failed: {text}");
    assert!(text.contains("arithmetization: R1CS"));
    assert!(text.contains("verifier accepts: true"), "{text}");
}

#[test]
fn plonkish_path_builds_and_self_checks_but_does_not_prove() {
    let ir = temp("iszero.ir.json", ISZERO_IR);
    let inputs = temp("honest.json", HONEST);
    let (ok, text) = run(&ir, &inputs, "plonkish");
    assert!(ok, "honest Plonkish run failed: {text}");
    assert!(text.contains("arithmetization: Plonkish"));
    assert!(text.contains("gate(s) and"), "should self-check gates and copies: {text}");
    // Honest about the boundary: lowered and checked, not proved.
    assert!(text.contains("no Plonkish prover yet"), "{text}");
    assert!(!text.contains("verifier accepts"), "Plonkish must not claim a proof: {text}");
}

#[test]
fn the_determinacy_record_is_identical_on_both_paths() {
    // The heart of F.2: the frontend's soundness verdict is inherited by
    // whichever arithmetization is chosen, verbatim.
    let ir = temp("iszero.ir.json", ISZERO_IR);
    let inputs = temp("honest.json", HONEST);
    let (_, r1cs_text) = run(&ir, &inputs, "r1cs");
    let (_, plonk_text) = run(&ir, &inputs, "plonkish");

    let line = |text: &str| {
        text.lines()
            .find(|l| l.starts_with("determinacy:"))
            .map(str::to_string)
            .unwrap_or_default()
    };
    let d1 = line(&r1cs_text);
    let d2 = line(&plonk_text);
    assert!(!d1.is_empty(), "no determinacy line on R1CS path: {r1cs_text}");
    assert_eq!(d1, d2, "the determinacy record differs across arithmetizations");
    assert!(d1.contains("proved"));
}

#[test]
fn a_forgery_is_rejected_by_both_arithmetizations() {
    // The determinacy guarantee must survive the choice of arithmetization:
    // the phase-0 forgery fails to build either way, at the same assertion.
    let ir = temp("iszero.ir.json", ISZERO_IR);
    let inputs = temp("forged.json", FORGED);
    for arith in ["r1cs", "plonkish"] {
        let (ok, text) = run(&ir, &inputs, arith);
        assert!(!ok, "the forgery was accepted under --arith {arith}: {text}");
        assert!(text.contains("NOT satisfied"), "{arith}: {text}");
        assert!(text.contains("(x * out) == 0"), "should name the failing assertion ({arith}): {text}");
    }
}

#[test]
fn an_unknown_arithmetization_is_rejected() {
    let ir = temp("iszero.ir.json", ISZERO_IR);
    let inputs = temp("honest.json", HONEST);
    let (ok, text) = run(&ir, &inputs, "stark");
    assert!(!ok);
    assert!(text.contains("unknown arithmetization 'stark'"), "{text}");
}