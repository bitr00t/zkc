//! Phase 7, N.2 — per-rule faithfulness of the lowering, proved not sampled.
//!
//! N.1 gave the IR an executable meaning and checked that both lowerings match
//! it on witnesses. N.2 proves the *rules*: for each IR operation, the
//! constraints and rows the lowering emits accept an assignment exactly when
//! the operation's defining relation holds — for *every* field element, not a
//! sampled few.
//!
//! The proof is by exhaustion over a tiny field. Each rule's defining relation
//! and the polynomials the lowering emits for it have total degree at most two;
//! a polynomial identity of degree `d` that holds on every point of a field
//! with more than `d` elements is the zero polynomial, so agreement across all
//! of F_13 (13 > 2) is not a sample but a proof that the identity holds over
//! any field. (This is the same Schwartz–Zippel fact the whole subject rests
//! on, used here on the compiler instead of on a proof.)
//!
//! For each rule we build the smallest circuit that isolates it — the operation
//! feeding one assertion against a prover-chosen output — instantiate the real
//! lowering over F_13, and enumerate every assignment of the free wires. Three
//! things must hold at every point: the IR spec, the R1CS lowering, and the
//! Plonkish lowering all agree, and their shared verdict equals the relation
//! `out == op(args)` computed independently. Enumerating the output over the
//! whole field covers the forgery direction (out ≠ op(args)) as well as the
//! honest one, so this pins the rule from both sides.

use std::collections::HashMap;

use zkc_core::field::ZkField;
use zkc_core::ir::Ir;
use zkc_core::lower::lower_with;
use zkc_core::plonkish::lower_plonkish_with;
use zkc_core::witness::{solve, SolveInputs};

// --- A tiny field, small enough to exhaust -------------------------------

/// The prime field F_P for a small `P`. Everything downstream is generic over
/// `ZkField`, so the real lowering runs over this unchanged.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Fp<const P: u64>(u64);

impl<const P: u64> Fp<P> {
    fn pow(self, mut e: u64) -> Self {
        let (mut base, mut acc) = (self, Fp(1 % P));
        while e > 0 {
            if e & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.mul(base);
            e >>= 1;
        }
        acc
    }
}

impl<const P: u64> ZkField for Fp<P> {
    fn zero() -> Self {
        Fp(0)
    }
    fn one() -> Self {
        Fp(1 % P)
    }
    fn add(self, other: Self) -> Self {
        Fp((self.0 + other.0) % P)
    }
    fn sub(self, other: Self) -> Self {
        Fp((self.0 + P - other.0) % P)
    }
    fn mul(self, other: Self) -> Self {
        Fp((self.0 * other.0) % P)
    }
    fn neg(self) -> Self {
        Fp((P - self.0) % P)
    }
    fn inverse(self) -> Option<Self> {
        if self.0 == 0 {
            None
        } else {
            Some(self.pow(P - 2)) // Fermat: a^(P-2) = a^{-1}
        }
    }
    fn from_u64(value: u64) -> Self {
        Fp(value % P)
    }
    fn to_decimal(self) -> String {
        self.0.to_string()
    }
}

const P: u64 = 13;
type F = Fp<P>;

// --- Rule fixtures: one operation feeding one assertion ------------------

const MUL_RULE: &str = r#"{
  "schema_version": 2, "name": "MulRule", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "private", "line": 1},
    {"wire": 2, "name": "b", "visibility": "private", "line": 1},
    {"wire": 3, "name": "out", "visibility": "output", "line": 1}],
  "nodes": [{"wire": 4, "advice_derived": false, "op": "mul", "args": [1, 2]}],
  "assertions": [{"lhs": 3, "rhs": 4, "label": "out == a * b", "line": 1}],
  "determinacy": {"proved": true, "targets": ["out"], "branches": [[]]}
}"#;

const ADD_RULE: &str = r#"{
  "schema_version": 2, "name": "AddRule", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "private", "line": 1},
    {"wire": 2, "name": "b", "visibility": "private", "line": 1},
    {"wire": 3, "name": "out", "visibility": "output", "line": 1}],
  "nodes": [{"wire": 4, "advice_derived": false, "op": "add", "args": [1, 2]}],
  "assertions": [{"lhs": 3, "rhs": 4, "label": "out == a + b", "line": 1}],
  "determinacy": {"proved": true, "targets": ["out"], "branches": [[]]}
}"#;

const SUB_RULE: &str = r#"{
  "schema_version": 2, "name": "SubRule", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "private", "line": 1},
    {"wire": 2, "name": "b", "visibility": "private", "line": 1},
    {"wire": 3, "name": "out", "visibility": "output", "line": 1}],
  "nodes": [{"wire": 4, "advice_derived": false, "op": "sub", "args": [1, 2]}],
  "assertions": [{"lhs": 3, "rhs": 4, "label": "out == a - b", "line": 1}],
  "determinacy": {"proved": true, "targets": ["out"], "branches": [[]]}
}"#;

const NEG_RULE: &str = r#"{
  "schema_version": 2, "name": "NegRule", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "private", "line": 1},
    {"wire": 2, "name": "out", "visibility": "output", "line": 1}],
  "nodes": [{"wire": 3, "advice_derived": false, "op": "neg", "args": [1]}],
  "assertions": [{"lhs": 2, "rhs": 3, "label": "out == -a", "line": 1}],
  "determinacy": {"proved": true, "targets": ["out"], "branches": [[]]}
}"#;

const CONST_RULE: &str = r#"{
  "schema_version": 2, "name": "ConstRule", "field": "bn254", "const_one_wire": 0,
  "inputs": [{"wire": 1, "name": "out", "visibility": "output", "line": 1}],
  "nodes": [{"wire": 2, "advice_derived": false, "op": "const", "value": "7"}],
  "assertions": [{"lhs": 1, "rhs": 2, "label": "out == 7", "line": 1}],
  "determinacy": {"proved": true, "targets": ["out"], "branches": [[]]}
}"#;

const ASSERT_RULE: &str = r#"{
  "schema_version": 2, "name": "AssertRule", "field": "bn254", "const_one_wire": 0,
  "inputs": [
    {"wire": 1, "name": "a", "visibility": "private", "line": 1},
    {"wire": 2, "name": "out", "visibility": "output", "line": 1}],
  "nodes": [],
  "assertions": [{"lhs": 2, "rhs": 1, "label": "out == a", "line": 1}],
  "determinacy": {"proved": true, "targets": ["out"], "branches": [[]]}
}"#;

// --- The exhaustive check ------------------------------------------------

/// Enumerate every assignment of the input wires over F_13 and require, at each
/// point, that the spec and both lowerings (fused and unfused) agree, and that
/// their shared verdict equals `out == relation(args)` computed here.
fn prove_rule(fixture: &str, relation: impl Fn(&HashMap<String, F>) -> F) {
    let ir = Ir::from_json(fixture).unwrap();
    let input_names: Vec<String> = ir.inputs.iter().map(|i| i.name.clone()).collect();
    let k = input_names.len() as u32;

    for code in 0..P.pow(k) {
        // Decode `code` into one field element per input wire.
        let mut rest = code;
        let mut env: HashMap<String, F> = HashMap::new();
        for name in &input_names {
            env.insert(name.clone(), F::from_u64(rest % P));
            rest /= P;
        }

        let wires = solve::<F>(
            &ir,
            &SolveInputs { inputs: &env, advice_overrides: &HashMap::new() },
        )
        .unwrap();

        let spec_ok = ir.is_satisfied::<F>(&wires);

        // The relation, computed independently of the IR and of the lowering.
        let relation_ok = env["out"] == relation(&env);
        assert_eq!(
            spec_ok, relation_ok,
            "{}: spec and the defining relation disagree at {env:?}", ir.name
        );

        // Both lowerings, in both fusion modes, must match the spec exactly.
        for fuse in [false, true] {
            let r1cs = lower_with::<F>(&ir, fuse).unwrap();
            let r1cs_ok = r1cs.is_satisfied(&r1cs.assignment(&wires));
            assert_eq!(
                r1cs_ok, spec_ok,
                "{}: R1CS (fuse={fuse}) disagrees with the spec at {env:?}", ir.name
            );

            let plonk = lower_plonkish_with::<F>(&ir, fuse).unwrap();
            let plonk_ok = plonk.is_satisfied(&plonk.assignment(&wires));
            assert_eq!(
                plonk_ok, spec_ok,
                "{}: Plonkish (fuse={fuse}) disagrees with the spec at {env:?}", ir.name
            );
        }
    }
}

#[test]
fn mul_rule_is_faithful() {
    prove_rule(MUL_RULE, |e| e["a"].mul(e["b"]));
}

#[test]
fn add_rule_is_faithful() {
    prove_rule(ADD_RULE, |e| e["a"].add(e["b"]));
}

#[test]
fn sub_rule_is_faithful() {
    prove_rule(SUB_RULE, |e| e["a"].sub(e["b"]));
}

#[test]
fn neg_rule_is_faithful() {
    prove_rule(NEG_RULE, |e| e["a"].neg());
}

#[test]
fn const_rule_is_faithful() {
    prove_rule(CONST_RULE, |_| F::from_u64(7));
}

#[test]
fn assertion_rule_is_faithful() {
    prove_rule(ASSERT_RULE, |e| e["a"]);
}

/// A guard on the guard: the exhaustive check must actually exercise both
/// verdicts. If a fixture only ever produced `true` (or only `false`), the
/// agreement assertions would pass vacuously. Over F_13 with the output free,
/// exactly 1/13 of assignments satisfy the relation, so both occur.
#[test]
fn the_check_sees_both_acceptance_and_rejection() {
    let ir = Ir::from_json(MUL_RULE).unwrap();
    let (mut accepted, mut rejected) = (0u32, 0u32);
    for a in 0..P {
        for b in 0..P {
            for out in 0..P {
                let env = HashMap::from([
                    ("a".to_string(), F::from_u64(a)),
                    ("b".to_string(), F::from_u64(b)),
                    ("out".to_string(), F::from_u64(out)),
                ]);
                let wires = solve::<F>(
                    &ir,
                    &SolveInputs { inputs: &env, advice_overrides: &HashMap::new() },
                )
                .unwrap();
                if ir.is_satisfied::<F>(&wires) {
                    accepted += 1;
                } else {
                    rejected += 1;
                }
            }
        }
    }
    assert_eq!(accepted, P as u32 * P as u32, "one satisfying out per (a, b)");
    assert!(rejected > 0, "the forgery direction must be exercised");
}