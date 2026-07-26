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
use zkc_core::plonkish::{lower_plonkish_with, Cell, Column, Plonkish};
use zkc_core::r1cs::R1cs;
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

// --- Phase 7, N.3: a mutation harness — proof the checker has teeth ------
//
// N.2 proved the real lowering agrees with the spec everywhere. It follows that
// *any* corruption of the lowering that changes its behaviour must disagree
// with the spec somewhere — so N.1/N.2's check would catch it. N.3 makes that
// argument concrete and keeps it honest: it deliberately breaks each rule and
// confirms the check flags the break. The invariant asserted is the anti-vacuity
// property — every mutation that changes behaviour (differs from the honest
// lowering) is caught by the spec — plus the demand that real, behaviour-changing
// mutations actually exist, so the check is never passing on nothing.

/// Every consistent full-wire assignment for a fixture (inputs enumerated over
/// F_13, intermediates solved).
fn all_assignments(ir: &Ir) -> Vec<Vec<F>> {
    let input_names: Vec<String> = ir.inputs.iter().map(|i| i.name.clone()).collect();
    let k = input_names.len() as u32;
    (0..P.pow(k))
        .map(|code| {
            let mut rest = code;
            let mut env = std::collections::HashMap::new();
            for name in &input_names {
                env.insert(name.clone(), F::from_u64(rest % P));
                rest /= P;
            }
            solve::<F>(ir, &SolveInputs { inputs: &env, advice_overrides: &HashMap::new() }).unwrap()
        })
        .collect()
}

fn r1cs_verdicts(r: &R1cs<F>, asg: &[Vec<F>]) -> Vec<bool> {
    asg.iter().map(|w| r.is_satisfied(&r.assignment(w))).collect()
}
fn plonk_verdicts(p: &Plonkish<F>, asg: &[Vec<F>]) -> Vec<bool> {
    asg.iter().map(|w| p.is_satisfied(&p.assignment(w))).collect()
}
fn spec_verdicts(ir: &Ir, asg: &[Vec<F>]) -> Vec<bool> {
    asg.iter().map(|w| ir.is_satisfied::<F>(w)).collect()
}

/// Labelled corruptions of a lowered R1CS: drop a constraint, shift one by a
/// constant, and perturb a coefficient.
fn r1cs_mutants(base: &R1cs<F>) -> Vec<(String, R1cs<F>)> {
    let mut out = Vec::new();
    for i in 0..base.constraints.len() {
        let mut drop = base.clone();
        drop.constraints.remove(i);
        out.push((format!("drop R1CS constraint {i}"), drop));

        let mut shift = base.clone();
        shift.constraints[i].c.terms.push((0, F::one())); // + 1·(const-one)
        out.push((format!("shift R1CS constraint {i} by 1"), shift));

        if let Some(term) = base.constraints[i].c.terms.first() {
            let mut bump = base.clone();
            bump.constraints[i].c.terms[0] = (term.0, term.1.add(F::one()));
            out.push((format!("perturb a coefficient of R1CS constraint {i}"), bump));
        }
    }
    out
}

/// Labelled corruptions of a lowered Plonkish system: drop a row, flip or bump
/// a selector, and route a bogus copy constraint.
fn plonkish_mutants(base: &Plonkish<F>) -> Vec<(String, Plonkish<F>)> {
    let mut out = Vec::new();
    for i in 0..base.rows.len() {
        // Neutralise the gate (all selectors zero ⇒ 0 == 0, always satisfied)
        // rather than removing the row, so the copy and public-cell indices that
        // reference rows by position stay valid. The effect is the same: the
        // constraint this row carried is gone.
        let mut drop = base.clone();
        let r = &mut drop.rows[i];
        r.q_l = F::zero();
        r.q_r = F::zero();
        r.q_o = F::zero();
        r.q_m = F::zero();
        r.q_c = F::zero();
        out.push((format!("neutralise Plonkish row {i}'s gate"), drop));

        for (name, sel) in [("output", 2u8), ("product", 3), ("constant", 4)] {
            let mut m = base.clone();
            let r = &mut m.rows[i];
            match sel {
                2 => r.q_o = r.q_o.add(F::one()),
                3 => r.q_m = r.q_m.add(F::one()),
                _ => r.q_c = r.q_c.add(F::one()),
            }
            out.push((format!("bump row {i} {name} selector"), m));
        }
    }
    // A misrouted/bogus copy: demand two cells of the first row agree. Where
    // they hold different wires this rejects honest witnesses; where they don't
    // it is a no-op — either way the anti-vacuity invariant must hold.
    if !base.rows.is_empty() {
        let mut m = base.clone();
        m.copies.push((
            Cell { row: 0, column: Column::A },
            Cell { row: 0, column: Column::B },
        ));
        out.push(("route a bogus copy constraint".to_string(), m));
    }
    out
}

/// The core N.3 invariant, per fixture: every behaviour-changing mutation is
/// caught by the spec, and at least one such mutation exists.
fn assert_check_has_teeth(fixture: &str) {
    let ir = Ir::from_json(fixture).unwrap();
    let asg = all_assignments(&ir);
    let spec = spec_verdicts(&ir, &asg);

    let r1cs = lower_with::<F>(&ir, false).unwrap();
    let plonk = lower_plonkish_with::<F>(&ir, false).unwrap();
    let r1cs_honest = r1cs_verdicts(&r1cs, &asg);
    let plonk_honest = plonk_verdicts(&plonk, &asg);

    let mut caught = 0;

    for (label, m) in r1cs_mutants(&r1cs) {
        let v = r1cs_verdicts(&m, &asg);
        let differs = v.iter().zip(&r1cs_honest).any(|(a, b)| a != b);
        let flagged = v.iter().zip(&spec).any(|(a, b)| a != b);
        assert_eq!(differs, flagged, "{}: '{label}' changed behaviour without being caught", ir.name);
        caught += flagged as usize;
    }
    for (label, m) in plonkish_mutants(&plonk) {
        let v = plonk_verdicts(&m, &asg);
        let differs = v.iter().zip(&plonk_honest).any(|(a, b)| a != b);
        let flagged = v.iter().zip(&spec).any(|(a, b)| a != b);
        assert_eq!(differs, flagged, "{}: '{label}' changed behaviour without being caught", ir.name);
        caught += flagged as usize;
    }

    assert!(caught > 0, "{}: no mutation was caught — the check is toothless here", ir.name);
}

#[test]
fn mutation_harness_catches_every_behaviour_changing_lowering() {
    for fixture in [MUL_RULE, ADD_RULE, SUB_RULE, NEG_RULE, CONST_RULE, ASSERT_RULE] {
        assert_check_has_teeth(fixture);
    }
}

#[test]
fn dropping_a_constraint_admits_a_forgery_the_spec_rejects() {
    // The named case. With the mul constraint gone, R1CS accepts every
    // assignment; the spec still rejects those where out ≠ a·b, so they diverge.
    let ir = Ir::from_json(MUL_RULE).unwrap();
    let asg = all_assignments(&ir);
    let spec = spec_verdicts(&ir, &asg);

    let mut broken = lower_with::<F>(&ir, false).unwrap();
    broken.constraints.clear();
    let v = r1cs_verdicts(&broken, &asg);

    assert!(v.iter().all(|&ok| ok), "an empty R1CS accepts everything");
    assert!(v.iter().zip(&spec).any(|(m, s)| m != s), "the spec rejects the forgeries it now admits");
}

#[test]
fn flipping_a_gate_selector_is_caught() {
    // Negate the product selector on every row: the mul gate becomes -a·b, so
    // it accepts a different relation and diverges from the spec.
    let ir = Ir::from_json(MUL_RULE).unwrap();
    let asg = all_assignments(&ir);
    let spec = spec_verdicts(&ir, &asg);

    let mut p = lower_plonkish_with::<F>(&ir, false).unwrap();
    for row in p.rows.iter_mut() {
        row.q_m = row.q_m.neg();
    }
    let v = plonk_verdicts(&p, &asg);
    assert!(v.iter().zip(&spec).any(|(m, s)| m != s), "a flipped q_m must diverge from the spec");
}

#[test]
fn a_bogus_copy_constraint_rejects_honest_witnesses_and_is_caught() {
    // Misrouting the wiring — here, demanding two independent inputs agree —
    // makes the lowering reject assignments the spec accepts.
    let ir = Ir::from_json(MUL_RULE).unwrap();
    let asg = all_assignments(&ir);
    let spec = spec_verdicts(&ir, &asg);

    let mut p = lower_plonkish_with::<F>(&ir, false).unwrap();
    p.copies.push((
        Cell { row: 0, column: Column::A },
        Cell { row: 0, column: Column::B },
    ));
    let v = plonk_verdicts(&p, &asg);
    assert!(v.iter().zip(&spec).any(|(m, s)| m != s), "a bogus copy must reject some honest witness");
}

#[test]
fn the_honest_lowering_is_never_flagged() {
    // The baseline the harness measures against: with no mutation, both
    // lowerings agree with the spec on every assignment (no false positives).
    for fixture in [MUL_RULE, ADD_RULE, SUB_RULE, NEG_RULE, CONST_RULE, ASSERT_RULE] {
        let ir = Ir::from_json(fixture).unwrap();
        let asg = all_assignments(&ir);
        let spec = spec_verdicts(&ir, &asg);
        let r1cs = lower_with::<F>(&ir, false).unwrap();
        let plonk = lower_plonkish_with::<F>(&ir, false).unwrap();
        assert_eq!(r1cs_verdicts(&r1cs, &asg), spec, "{}: R1CS baseline", ir.name);
        assert_eq!(plonk_verdicts(&plonk, &asg), spec, "{}: Plonkish baseline", ir.name);
    }
}