//! End-to-end STARK tests (phase 5, Workstream I.2) — the phase's payoff.
//!
//! The claim the whole roadmap has been building toward: an own prover, no
//! arkworks, that proves an honest witness and rejects the phase-0 forgery.
//! These tests run the FRI-STARK over the hand-written Goldilocks field with a
//! stand-in hash, on the Plonkish circuits phase 4 produces.

use std::collections::HashMap;

use zkc_core::field::ZkField;
use zkc_core::fri::FriConfig;
use zkc_core::goldilocks::Goldilocks;
use zkc_core::hash::{Digest, Hasher};
use zkc_core::ir::Ir;
use zkc_core::plonkish::lower_plonkish;
use zkc_core::air::{Air, Trace};
use zkc_core::plonkish::{Cell, Column, Plonkish, Row};
use zkc_core::stark::{prove, prove_with_trace, verify, verify_with_air};
use zkc_core::witness::{solve, SolveInputs};

type F = Goldilocks;

#[derive(Clone)]
struct ToyHash;
fn g(v: u64) -> F {
    F::from_u64(v)
}
fn sbox(x: F) -> F {
    let x2 = ZkField::mul(x, x);
    let x4 = ZkField::mul(x2, x2);
    ZkField::mul(ZkField::mul(x4, x2), x)
}
impl Hasher<F> for ToyHash {
    const WIDTH: usize = 1;
    fn hash(input: &[F]) -> Digest<F> {
        let mut s = g(0x9E3779B97F4A7C15);
        for (i, x) in input.iter().enumerate() {
            s = sbox(ZkField::add(s, ZkField::add(*x, g(i as u64 + 1))));
        }
        Digest(vec![sbox(s)])
    }
    fn compress(l: &Digest<F>, r: &Digest<F>) -> Digest<F> {
        Self::hash(&[l.0[0], r.0[0]])
    }
}

const ISZERO_IR: &str = include_str!("/tmp/iszero.ir.json");

fn inputs(pairs: &[(&str, &str)]) -> HashMap<String, F> {
    pairs.iter().map(|(k, v)| (k.to_string(), F::from_decimal(v).unwrap())).collect()
}

#[test]
fn an_honest_witness_proves_and_verifies() {
    // x = 0 forces out = 1; the honest witness must yield an accepted proof.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let circuit = lower_plonkish::<F>(&ir).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs(&[("x", "0"), ("out", "1")]), advice_overrides: &HashMap::new() },
    )
    .unwrap();

    let config = FriConfig::default();
    let proof = prove::<F, ToyHash>(&circuit, &wires, &config);
    assert!(
        verify::<F, ToyHash>(&circuit, &proof, &config).is_ok(),
        "honest witness did not verify"
    );
}

#[test]
fn the_phase_zero_forgery_yields_no_accepted_proof() {
    // The security claim, end to end and cryptography-side this time. The
    // forgery sets inv = 0 with x = 5, out = 1, so the gate `x·out = 0` fails.
    // The quotient Q = C/Z_H is then NOT a polynomial, FRI cannot make it look
    // low-degree, and the consistency check C = Q·Z_H fails at the queried
    // points. Either way: no accepted proof.
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let circuit = lower_plonkish::<F>(&ir).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("x", "5"), ("out", "1")]),
            advice_overrides: &inputs(&[("inv", "0")]),
        },
    )
    .unwrap();

    let config = FriConfig::default();
    let proof = prove::<F, ToyHash>(&circuit, &wires, &config);
    assert!(
        verify::<F, ToyHash>(&circuit, &proof, &config).is_err(),
        "the phase-0 forgery produced an accepted proof"
    );
}

#[test]
fn a_tampered_proof_is_rejected() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let circuit = lower_plonkish::<F>(&ir).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs(&[("x", "0"), ("out", "1")]), advice_overrides: &HashMap::new() },
    )
    .unwrap();

    let config = FriConfig::default();
    let mut proof = prove::<F, ToyHash>(&circuit, &wires, &config);

    // Corrupt an opened trace value: the consistency check or Merkle must catch it.
    proof.queries[0].lo.a = g(999999);
    assert!(
        verify::<F, ToyHash>(&circuit, &proof, &config).is_err(),
        "a tampered trace opening was accepted"
    );
}

#[test]
fn the_verifier_binds_to_the_transcript() {
    // A proof made under one transcript must not verify under a mismatched
    // config (different query count changes the challenges).
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let circuit = lower_plonkish::<F>(&ir).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs(&[("x", "0"), ("out", "1")]), advice_overrides: &HashMap::new() },
    )
    .unwrap();

    let proof = prove::<F, ToyHash>(&circuit, &wires, &FriConfig { blowup: 4, num_queries: 20 });
    // Verify with a different query count: the transcript diverges, so the
    // recomputed query positions will not match.
    let result = verify::<F, ToyHash>(&circuit, &proof, &FriConfig { blowup: 4, num_queries: 24 });
    assert!(result.is_err(), "proof verified under a mismatched transcript");
}


#[test]
fn a_wiring_violation_is_caught_by_the_permutation_argument() {
    // The capability the permutation argument adds. Build a tiny circuit whose
    // two rows carry NO gate (all selectors zero, so the gate identity is 0=0
    // everywhere) but whose two cells are wired together by a copy constraint.
    // An honest trace puts the same value in both; a violating trace puts
    // different values in them. The gates are satisfied either way — only the
    // wiring argument can tell the two apart.
    let zero = F::zero();
    let row = |origin: &str| Row {
        q_l: zero, q_r: zero, q_o: zero, q_m: zero, q_c: zero,
        cells: [Some(0), None, None],
        origin: origin.to_string(),
    };
    let (row0, row1) = (row("wire cell A"), row("wire cell B"));
    let circuit = Plonkish {
        rows: vec![row0, row1],
        // wire 0 sits in (row 0, col A) and (row 1, col A): they must agree.
        copies: vec![(Cell::new(0, Column::A), Cell::new(1, Column::A))],
        public_cells: vec![],
        names: std::collections::HashMap::new(),
    };
    let air = Air::from_plonkish(&circuit);
    let config = FriConfig::default();

    // Honest: both cells hold 42. The permutation argument must accept.
    let honest = Trace { a: vec![g(42), g(42)], b: vec![g(0), g(0)], c: vec![g(0), g(0)] };
    let proof = prove_with_trace::<F, ToyHash>(&air, &honest, &config);
    assert!(
        verify_with_air::<F, ToyHash>(&air, &proof, &config).is_ok(),
        "honest wiring rejected"
    );

    // Violating: the two wired cells disagree (5 vs 7). Gates still hold (all
    // selectors zero), but the wiring is broken — this must be rejected.
    let broken = Trace { a: vec![g(5), g(7)], b: vec![g(0), g(0)], c: vec![g(0), g(0)] };
    let proof = prove_with_trace::<F, ToyHash>(&air, &broken, &config);
    assert!(
        verify_with_air::<F, ToyHash>(&air, &proof, &config).is_err(),
        "a broken wire slipped past the permutation argument"
    );
}
