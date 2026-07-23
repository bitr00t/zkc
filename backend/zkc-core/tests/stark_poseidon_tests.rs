//! The STARK's security claims, re-run under the *reviewed* hash
//! (phase 5, hash hardening).
//!
//! `stark_tests.rs` establishes honest-verifies / forgery-rejected /
//! wiring-enforced against the transparent stand-in `ToyHash`. The whole point
//! of writing the prover against a `Hasher` trait was that swapping in a
//! reviewed hash is a leaf change that leaves those claims intact. These tests
//! are that swap made good: the identical properties, now under Poseidon over
//! Goldilocks with Plonky2's canonical parameters. Nothing in `stark.rs`,
//! `fri.rs`, `merkle.rs` or `transcript.rs` changed to make this compile — only
//! the type parameter `H`.

use std::collections::HashMap;

use zkc_core::air::{Air, Trace};
use zkc_core::field::ZkField;
use zkc_core::fri::FriConfig;
use zkc_core::goldilocks::Goldilocks;
use zkc_core::ir::Ir;
use zkc_core::plonkish::{lower_plonkish, Cell, Column, Plonkish, Row};
use zkc_core::poseidon::PoseidonGoldilocks;
use zkc_core::stark::{prove, prove_with_trace, verify, verify_with_air};
use zkc_core::witness::{solve, SolveInputs};

type F = Goldilocks;
type H = PoseidonGoldilocks;

const ISZERO_IR: &str = include_str!("/tmp/iszero.ir.json");

fn g(v: u64) -> F {
    F::from_u64(v)
}
fn inputs(pairs: &[(&str, &str)]) -> HashMap<String, F> {
    pairs.iter().map(|(k, v)| (k.to_string(), F::from_decimal(v).unwrap())).collect()
}

#[test]
fn honest_witness_proves_and_verifies_under_poseidon() {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let circuit = lower_plonkish::<F>(&ir).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs(&[("x", "0"), ("out", "1")]), advice_overrides: &HashMap::new() },
    )
    .unwrap();

    let config = FriConfig::default();
    let proof = prove::<F, H>(&circuit, &wires, &config);
    assert!(
        verify::<F, H>(&circuit, &proof, &config).is_ok(),
        "honest witness did not verify under Poseidon"
    );
}

#[test]
fn phase_zero_forgery_rejected_under_poseidon() {
    // inv = 0 with x = 5, out = 1: the gate x·out = 0 fails, so Q = C/Z_H is
    // not a polynomial and the proof cannot be accepted — hash notwithstanding.
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
    let proof = prove::<F, H>(&circuit, &wires, &config);
    assert!(
        verify::<F, H>(&circuit, &proof, &config).is_err(),
        "the phase-0 forgery produced an accepted proof under Poseidon"
    );
}

#[test]
fn wiring_violation_caught_under_poseidon() {
    let zero = F::zero();
    let row = |origin: &str| Row {
        q_l: zero, q_r: zero, q_o: zero, q_m: zero, q_c: zero,
        cells: [Some(0), None, None],
        origin: origin.to_string(),
    };
    let circuit = Plonkish {
        rows: vec![row("wire cell A"), row("wire cell B")],
        copies: vec![(Cell::new(0, Column::A), Cell::new(1, Column::A))],
        public_cells: vec![],
        names: HashMap::new(),
    };
    let air = Air::from_plonkish(&circuit);
    let config = FriConfig::default();

    let honest = Trace { a: vec![g(42), g(42)], b: vec![g(0), g(0)], c: vec![g(0), g(0)] };
    let proof = prove_with_trace::<F, H>(&air, &honest, &config);
    assert!(verify_with_air::<F, H>(&air, &proof, &config).is_ok(), "honest wiring rejected under Poseidon");

    let broken = Trace { a: vec![g(5), g(7)], b: vec![g(0), g(0)], c: vec![g(0), g(0)] };
    let proof = prove_with_trace::<F, H>(&air, &broken, &config);
    assert!(
        verify_with_air::<F, H>(&air, &proof, &config).is_err(),
        "a broken wire slipped past the permutation argument under Poseidon"
    );
}