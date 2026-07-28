//! DEEP: the committed columns are inside the low-degree test (phase 5, the
//! last core soundness boundary).
//!
//! What the STARK used to prove, precisely: the *quotient* is low-degree, and
//! the constraint identity holds at the positions the queries happened to open.
//! The trace and the grand-product column `Z` were committed and opened, but
//! never themselves tested — nothing in the protocol asked them to be
//! polynomials, and nothing looked at them anywhere a query did not land.
//!
//! That is a spot check, and this file is about the difference between a spot
//! check and a proof. The prover exercised here
//! ([`prove_with_corrupted_column`]) is not a clumsy liar: it commits a column
//! that differs from the honest low-degree extension at exactly one position,
//! and everything else about it is impeccable. The quotient is genuinely
//! low-degree, because it is built from the honest polynomial. The identity
//! holds at every position but one. Every Merkle opening checks out, because
//! the corrupted value is the committed value. Under the old protocol the only
//! thing that could notice was a query landing on that one position — and the
//! query positions are a public function of the commitment, so a prover can
//! simply retry until they do not.
//!
//! The tests below find such a position, confirm no query opens it, and watch
//! the proof be rejected anyway.

use std::collections::HashMap;
use std::collections::HashSet;

use zkc_core::air::Air;
use zkc_core::field::ZkField;
use zkc_core::fri::FriConfig;
use zkc_core::goldilocks::Goldilocks;
use zkc_core::hash::{Digest, Hasher};
use zkc_core::ir::Ir;
use zkc_core::plonkish::lower_plonkish;
use zkc_core::stark::{
    prove_with_corrupted_column, prove_with_trace, verify_with_air, StarkProof,
};
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
        let mut s = g(0x9E37_79B9_7F4A_7C15);
        for (i, x) in input.iter().enumerate() {
            s = sbox(ZkField::add(s, ZkField::add(*x, g(i as u64 + 1))));
        }
        Digest(vec![sbox(s)])
    }
    fn compress(l: &Digest<F>, r: &Digest<F>) -> Digest<F> {
        Self::hash(&[l.0[0], r.0[0]])
    }
}

const ISZERO_IR: &str = include_str!("fixtures/iszero.ir.json");

fn inputs(pairs: &[(&str, &str)]) -> HashMap<String, F> {
    pairs.iter().map(|(k, v)| (k.to_string(), F::from_decimal(v).unwrap())).collect()
}

/// The IsZero circuit with its honest witness, as an AIR and a trace.
fn iszero() -> (Air<F>, zkc_core::air::Trace<F>) {
    let ir = Ir::from_json(ISZERO_IR).unwrap();
    let circuit = lower_plonkish::<F>(&ir).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs {
            inputs: &inputs(&[("x", "0"), ("out", "1")]),
            advice_overrides: &HashMap::new(),
        },
    )
    .unwrap();
    let air = Air::from_plonkish(&circuit);
    let trace = Air::trace(&circuit, &wires);
    (air, trace)
}

/// Every domain position any query opens. Under the previous protocol this was
/// the entire extent of the verifier's view of the trace.
fn opened_positions(proof: &StarkProof<F>, config: &FriConfig) -> HashSet<usize> {
    let half0 = proof.degree_bound * config.blowup / 2;
    proof
        .fri
        .queries
        .iter()
        .flat_map(|query| {
            let lo = query.index % half0;
            [lo, lo + half0]
        })
        .collect()
}

#[test]
fn the_honest_proof_still_verifies_through_the_deep_batch() {
    // The rewrite moved the constraint check out of the domain and put every
    // column into one low-degree test. Before asking what it rejects: it must
    // still accept.
    let (air, trace) = iszero();
    let config = FriConfig::default();
    let proof = prove_with_trace::<F, ToyHash>(&air, &trace, &config);
    assert!(
        verify_with_air::<F, ToyHash>(&air, &proof, &config).is_ok(),
        "the honest witness no longer verifies"
    );
}

#[test]
fn the_corruption_mechanism_itself_changes_nothing() {
    // A zero corruption must be indistinguishable from no corruption. Without
    // this the tests below would prove only that the alternative code path is
    // broken, which is not the claim.
    let (air, trace) = iszero();
    let config = FriConfig::default();
    let proof = prove_with_corrupted_column::<F, ToyHash>(&air, &trace, &config, 3, F::zero());
    assert!(
        verify_with_air::<F, ToyHash>(&air, &proof, &config).is_ok(),
        "a corruption of zero must leave an honest proof honest"
    );
}

#[test]
fn a_corrupted_column_is_refused_at_a_position_no_query_opens() {
    // The headline. Find a position the queries miss — a prover can grind for
    // one, since the positions follow publicly from the commitment — and watch
    // the proof fail anyway.
    let (air, trace) = iszero();
    let config = FriConfig { blowup: 4, num_queries: 8 };
    let domain_size = {
        let probe = prove_with_trace::<F, ToyHash>(&air, &trace, &config);
        probe.degree_bound * config.blowup
    };

    let mut chosen = None;
    for position in 0..domain_size {
        let proof = prove_with_corrupted_column::<F, ToyHash>(&air, &trace, &config, position, g(1));
        if !opened_positions(&proof, &config).contains(&position) {
            chosen = Some((position, proof));
            break;
        }
    }
    let (position, proof) = chosen.expect("some position escapes the queries");

    // The corrupted value is one the verifier never sees directly. Every
    // opening it does check is of an honest value.
    let opened = opened_positions(&proof, &config);
    assert!(!opened.contains(&position), "the test needs a position outside the queried set");
    assert!(opened.len() < domain_size, "the queries must not cover the domain");

    let outcome = verify_with_air::<F, ToyHash>(&air, &proof, &config);
    assert!(outcome.is_err(), "a corrupted column at position {position} was accepted");

    // And it fails for the right reason: not a broken opening, not the
    // constraint check, but the low-degree test — the corrupted column is now
    // part of what FRI is testing.
    // And it fails for exactly the right reason. The verifier got all the way
    // past the constraint check at ζ — which passes, because the quotient is
    // honest — and died in the low-degree test, on the column that was never
    // opened. That is the whole point: what refuses this proof is not an
    // inspection of the corrupted value but the fact that it is now part of
    // what FRI is testing.
    let reason = outcome.unwrap_err();
    assert_eq!(reason, "final FRI codeword is not constant (input was not low-degree)");
}

#[test]
fn no_position_escapes_the_low_degree_test() {
    // The difference between the old protocol and this one is the difference
    // between "probably caught" and "caught". A spot check has positions it
    // does not look at, by construction. This one does not: every single
    // position in the domain is refused.
    let (air, trace) = iszero();
    let config = FriConfig { blowup: 4, num_queries: 4 };
    let domain_size = {
        let probe = prove_with_trace::<F, ToyHash>(&air, &trace, &config);
        probe.degree_bound * config.blowup
    };

    for position in 0..domain_size {
        let proof = prove_with_corrupted_column::<F, ToyHash>(&air, &trace, &config, position, g(1));
        assert!(
            verify_with_air::<F, ToyHash>(&air, &proof, &config).is_err(),
            "a corrupted column at position {position} was accepted"
        );
    }
}

#[test]
fn an_invented_out_of_domain_value_is_refused() {
    // The constraint is checked at ζ now, so the six values claimed there are
    // load-bearing. Changing one must not go unnoticed.
    let (air, trace) = iszero();
    let config = FriConfig::default();

    for which in 0..6 {
        let mut proof = prove_with_trace::<F, ToyHash>(&air, &trace, &config);
        let ood = &mut proof.ood;
        let slot = match which {
            0 => &mut ood.a,
            1 => &mut ood.b,
            2 => &mut ood.c,
            3 => &mut ood.z,
            4 => &mut ood.z_next,
            _ => &mut ood.q,
        };
        *slot = slot.add(F::one());
        assert!(
            verify_with_air::<F, ToyHash>(&air, &proof, &config).is_err(),
            "an altered out-of-domain value (slot {which}) was accepted"
        );
    }
}

#[test]
fn the_quotient_commitment_is_bound_to_the_transcript() {
    // The quotient is committed before ζ is drawn, which is what stops the
    // prover choosing it to suit the point. Swapping the root changes ζ and
    // every batching challenge, so nothing downstream can still line up.
    let (air, trace) = iszero();
    let config = FriConfig::default();
    let mut proof = prove_with_trace::<F, ToyHash>(&air, &trace, &config);
    proof.q_root = Digest(vec![proof.q_root.0[0].add(F::one())]);
    assert!(
        verify_with_air::<F, ToyHash>(&air, &proof, &config).is_err(),
        "a substituted quotient root was accepted"
    );
}
