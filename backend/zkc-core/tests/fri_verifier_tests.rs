//! Phase 7, O — a complete in-circuit FRI verifier for one query.
//!
//! O.1 checked the algebraic fold; O.2 proved one fold inside an outer proof.
//! This closes the arc: the *authenticity* check too. A real (tiny) FRI proof is
//! produced under a circuit-friendly hash, and for one query the in-circuit
//! verifier Merkle-verifies both openings against the committed root, folds
//! them, and checks the fold against the constant final codeword — then that
//! whole verification is itself proved and verified as an outer STARK proof.
//! Tampering an authentication path breaks it, exactly as every phase before.

use std::collections::HashMap;

use zkc_core::field::{TwoAdicField, ZkField};
use zkc_core::fri::{coset_shift, prove as fri_prove, verify as fri_verify, FriConfig};
use zkc_core::goldilocks::Goldilocks;
use zkc_core::hash::{Digest, Hasher};
use zkc_core::ir::Ir;
use zkc_core::plonkish::lower_plonkish;
use zkc_core::stark::{prove as stark_prove, verify as stark_verify};
use zkc_core::transcript::Transcript;
use zkc_core::witness::{solve, SolveInputs};

type F = Goldilocks;

fn g(v: u64) -> F {
    F::from_u64(v)
}
fn sbox(x: F) -> F {
    let x2 = x.mul(x);
    let x4 = x2.mul(x2);
    x4.mul(x2).mul(x) // x^7
}

/// The circuit-friendly hash the in-circuit verifier speaks: a single leaf [v]
/// hashes to sbox(v + 1), and two digests compress to sbox(l + 2) + sbox(r + 3).
/// These are exactly the `hash_leaf` and `compress` gadgets, so a path that
/// verifies in the tree verifies in the circuit.
#[derive(Clone)]
struct CircuitHash;
impl Hasher<F> for CircuitHash {
    const WIDTH: usize = 1;
    fn hash(input: &[F]) -> Digest<F> {
        let mut acc = F::zero();
        for (i, x) in input.iter().enumerate() {
            acc = acc.add(x.add(g(i as u64 + 1)));
        }
        Digest(vec![sbox(acc)])
    }
    fn compress(l: &Digest<F>, r: &Digest<F>) -> Digest<F> {
        Digest(vec![sbox(l.0[0].add(g(2))).add(sbox(r.0[0].add(g(3))))])
    }
}

fn pow(base: F, mut e: u64) -> F {
    let (mut acc, mut b) = (F::one(), base);
    while e > 0 {
        if e & 1 == 1 {
            acc = acc.mul(b);
        }
        b = b.mul(b);
        e >>= 1;
    }
    acc
}

// The in-circuit verifier, compiled from examples/fri_verify_full.zkc.
const VERIFIER_IR: &str = include_str!("fixtures/fri_verify_full.ir.json");

/// A real one-round FRI proof and the verifier inputs for its first query.
fn proof_and_query_inputs() -> (HashMap<String, F>, FriConfig) {
    let degree_bound = 2usize;
    let config = FriConfig { blowup: 2, num_queries: 1 };
    let coeffs: Vec<F> = vec![g(7), g(3)]; // degree < 2

    let mut prover_t = Transcript::<_, CircuitHash>::new(&[g(1)]);
    let inner = fri_prove(&coeffs, degree_bound, &config, &mut prover_t);
    let mut verifier_t = Transcript::<_, CircuitHash>::new(&[g(1)]);
    assert!(
        fri_verify(&inner, degree_bound, &config, &mut verifier_t).is_ok(),
        "the inner FRI proof must verify"
    );

    // Replay for the folding challenge.
    let mut replay = Transcript::<_, CircuitHash>::new(&[g(1)]);
    let mut alphas = Vec::new();
    for root in &inner.roots {
        replay.absorb_digest(root);
        alphas.push(replay.challenge());
    }

    let query = &inner.queries[0];
    let layer = &query.layers[0];
    let domain = inner.domain_size;
    let half0 = domain / 2;
    let lo0 = query.index % half0;
    let gen = F::two_adic_generator(domain.trailing_zeros());
    let x = coset_shift::<F>().mul(pow(gen, lo0 as u64));

    let bit = |idx: usize, level: u32| g(((idx >> level) & 1) as u64);
    let sib = |op: &zkc_core::merkle::Opening<F>, level: usize| op.siblings[level].0[0];

    // The prover computes the honest witness — the hashes up each path and the
    // fold — with the same arithmetic the gadgets constrain. The circuit then
    // checks it: a wrong value fails a hash or Merkle assertion.
    let hash_leaf = |v: F| sbox(v.add(g(1)));
    let compress = |l: F, r: F| sbox(l.add(g(2))).add(sbox(r.add(g(3))));
    let mux = |sel: F, a: F, b: F| if sel == g(1) { a } else { b };
    let fold = |p: F, m: F, beta: F, xx: F| {
        xx.add(xx).inverse().unwrap().mul(xx.mul(p.add(m)).add(beta.mul(p.sub(m))))
    };

    let (lo, hi) = (layer.lo, layer.hi);
    let (lb0, lb1) = (bit(layer.lo_proof.index, 0), bit(layer.lo_proof.index, 1));
    let (ls0, ls1) = (sib(&layer.lo_proof, 0), sib(&layer.lo_proof, 1));
    let (hb0, hb1) = (bit(layer.hi_proof.index, 0), bit(layer.hi_proof.index, 1));
    let (hs0, hs1) = (sib(&layer.hi_proof, 0), sib(&layer.hi_proof, 1));
    let alpha = alphas[0];
    let (final0, final1) = (inner.final_poly[0], inner.final_poly[1]);
    let root = inner.roots[0].0[0];

    let lo_leaf = hash_leaf(lo);
    let lo_left0 = mux(lb0, ls0, lo_leaf);
    let lo_right0 = mux(lb0, lo_leaf, ls0);
    let lo_node0 = compress(lo_left0, lo_right0);
    let lo_left1 = mux(lb1, ls1, lo_node0);
    let lo_right1 = mux(lb1, lo_node0, ls1);
    let lo_root = compress(lo_left1, lo_right1);

    let hi_leaf = hash_leaf(hi);
    let hi_left0 = mux(hb0, hs0, hi_leaf);
    let hi_right0 = mux(hb0, hi_leaf, hs0);
    let hi_node0 = compress(hi_left0, hi_right0);
    let hi_left1 = mux(hb1, hs1, hi_node0);
    let hi_right1 = mux(hb1, hi_node0, hs1);
    let hi_root = compress(hi_left1, hi_right1);

    let folded = fold(lo, hi, alpha, x);

    let inputs: HashMap<String, F> = [
        ("lo", lo), ("hi", hi),
        ("lo_sib0", ls0), ("lo_sib1", ls1), ("lo_bit0", lb0), ("lo_bit1", lb1),
        ("hi_sib0", hs0), ("hi_sib1", hs1), ("hi_bit0", hb0), ("hi_bit1", hb1),
        ("root", root), ("alpha", alpha), ("x", x),
        ("final0", final0), ("final1", final1),
        // prover-supplied intermediate results the circuit verifies:
        ("lo_leaf", lo_leaf), ("lo_left0", lo_left0), ("lo_right0", lo_right0),
        ("lo_node0", lo_node0), ("lo_left1", lo_left1), ("lo_right1", lo_right1),
        ("lo_root", lo_root),
        ("hi_leaf", hi_leaf), ("hi_left0", hi_left0), ("hi_right0", hi_right0),
        ("hi_node0", hi_node0), ("hi_left1", hi_left1), ("hi_right1", hi_right1),
        ("hi_root", hi_root),
        ("folded", folded), ("accepted", g(1)),
    ]
    .iter()
    .map(|(k, v)| ((*k).to_string(), *v))
    .collect();

    (inputs, config)
}

#[test]
fn a_full_fri_query_is_verified_inside_an_outer_proof() {
    let (inputs, _config) = proof_and_query_inputs();
    let ir = Ir::from_json(VERIFIER_IR).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
    )
    .unwrap();
    let vcircuit = lower_plonkish::<F>(&ir).unwrap();

    // The complete verification — Merkle paths, fold, final check — is satisfied.
    assert!(
        vcircuit.is_satisfied(&vcircuit.assignment(&wires)),
        "the in-circuit verifier must accept a real, honest query"
    );

    // And proving it yields an outer proof that verifies: recursion over the
    // whole query, authentication paths included.
    let config = FriConfig::default();
    let outer = stark_prove::<F, CircuitHash>(&vcircuit, &wires, &config);
    assert!(
        stark_verify::<F, CircuitHash>(&vcircuit, &outer, &config).is_ok(),
        "the outer proof over the full query must verify"
    );
}

#[test]
fn a_tampered_authentication_path_breaks_the_verifier() {
    let (mut inputs, _config) = proof_and_query_inputs();
    let ir = Ir::from_json(VERIFIER_IR).unwrap();
    let vcircuit = lower_plonkish::<F>(&ir).unwrap();

    // Tamper one sibling on lo's authentication path: the recomputed root no
    // longer matches, so the Merkle check — and the whole verifier — rejects it.
    let sib = inputs.get_mut("lo_sib0").unwrap();
    *sib = sib.add(F::one());

    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
    )
    .unwrap();
    assert!(
        !vcircuit.is_satisfied(&vcircuit.assignment(&wires)),
        "a tampered authentication path must be rejected before proving"
    );

    let config = FriConfig::default();
    let forced = stark_prove::<F, CircuitHash>(&vcircuit, &wires, &config);
    assert!(
        stark_verify::<F, CircuitHash>(&vcircuit, &forced, &config).is_err(),
        "a forced outer proof over a tampered path must not verify"
    );
}

// --- In-circuit Fiat-Shamir --------------------------------------------------
//
// The verifier above trusted the fold challenge as an input. Here it is derived
// in-circuit from the layer commitment, so the prover cannot choose it after
// committing — the soundness Fiat-Shamir exists to provide, enforced by the
// circuit. For the transcript state [seed, root] and the circuit-friendly hash,
// the round-0 challenge is sbox(seed + root + 6); the test checks that against
// the real transcript before proving the whole verification.

const VERIFIER_FS_IR: &str = include_str!("fixtures/fri_verify_fs.ir.json");

fn fs_query_inputs() -> (HashMap<String, F>, F, F) {
    let degree_bound = 2usize;
    let config = FriConfig { blowup: 2, num_queries: 1 };
    let coeffs: Vec<F> = vec![g(7), g(3)];
    let seed = g(1);

    let mut prover_t = Transcript::<_, CircuitHash>::new(&[seed]);
    let inner = fri_prove(&coeffs, degree_bound, &config, &mut prover_t);
    let mut verifier_t = Transcript::<_, CircuitHash>::new(&[seed]);
    assert!(fri_verify(&inner, degree_bound, &config, &mut verifier_t).is_ok());

    let mut replay = Transcript::<_, CircuitHash>::new(&[seed]);
    let mut alphas = Vec::new();
    for root in &inner.roots {
        replay.absorb_digest(root);
        alphas.push(replay.challenge());
    }

    let query = &inner.queries[0];
    let layer = &query.layers[0];
    let domain = inner.domain_size;
    let half0 = domain / 2;
    let lo0 = query.index % half0;
    let gen = F::two_adic_generator(domain.trailing_zeros());
    let x = coset_shift::<F>().mul(pow(gen, lo0 as u64));
    let root = inner.roots[0].0[0];

    // Fiat-Shamir, in the field: derive the challenge from seed and root, and
    // confirm it is exactly what the transcript produced.
    let alpha_derived = sbox(seed.add(root).add(g(6)));
    assert_eq!(alpha_derived, alphas[0], "in-circuit Fiat-Shamir must match the transcript");

    let bit = |idx: usize, level: u32| g(((idx >> level) & 1) as u64);
    let sib = |op: &zkc_core::merkle::Opening<F>, level: usize| op.siblings[level].0[0];
    let hash_leaf = |v: F| sbox(v.add(g(1)));
    let compress = |l: F, r: F| sbox(l.add(g(2))).add(sbox(r.add(g(3))));
    let mux = |sel: F, a: F, b: F| if sel == g(1) { a } else { b };
    let fold = |p: F, m: F, beta: F, xx: F| {
        xx.add(xx).inverse().unwrap().mul(xx.mul(p.add(m)).add(beta.mul(p.sub(m))))
    };

    let (lo, hi) = (layer.lo, layer.hi);
    let (lb0, lb1) = (bit(layer.lo_proof.index, 0), bit(layer.lo_proof.index, 1));
    let (ls0, ls1) = (sib(&layer.lo_proof, 0), sib(&layer.lo_proof, 1));
    let (hb0, hb1) = (bit(layer.hi_proof.index, 0), bit(layer.hi_proof.index, 1));
    let (hs0, hs1) = (sib(&layer.hi_proof, 0), sib(&layer.hi_proof, 1));
    let (final0, final1) = (inner.final_poly[0], inner.final_poly[1]);

    let lo_leaf = hash_leaf(lo);
    let lo_left0 = mux(lb0, ls0, lo_leaf);
    let lo_right0 = mux(lb0, lo_leaf, ls0);
    let lo_node0 = compress(lo_left0, lo_right0);
    let lo_left1 = mux(lb1, ls1, lo_node0);
    let lo_right1 = mux(lb1, lo_node0, ls1);
    let lo_root = compress(lo_left1, lo_right1);
    let hi_leaf = hash_leaf(hi);
    let hi_left0 = mux(hb0, hs0, hi_leaf);
    let hi_right0 = mux(hb0, hi_leaf, hs0);
    let hi_node0 = compress(hi_left0, hi_right0);
    let hi_left1 = mux(hb1, hs1, hi_node0);
    let hi_right1 = mux(hb1, hi_node0, hs1);
    let hi_root = compress(hi_left1, hi_right1);
    let folded = fold(lo, hi, alpha_derived, x);

    let inputs: HashMap<String, F> = [
        ("lo", lo), ("hi", hi),
        ("lo_sib0", ls0), ("lo_sib1", ls1), ("lo_bit0", lb0), ("lo_bit1", lb1),
        ("hi_sib0", hs0), ("hi_sib1", hs1), ("hi_bit0", hb0), ("hi_bit1", hb1),
        ("root", root), ("seed", seed), ("x", x),
        ("final0", final0), ("final1", final1),
        ("lo_leaf", lo_leaf), ("lo_left0", lo_left0), ("lo_right0", lo_right0),
        ("lo_node0", lo_node0), ("lo_left1", lo_left1), ("lo_right1", lo_right1),
        ("lo_root", lo_root),
        ("hi_leaf", hi_leaf), ("hi_left0", hi_left0), ("hi_right0", hi_right0),
        ("hi_node0", hi_node0), ("hi_left1", hi_left1), ("hi_right1", hi_right1),
        ("hi_root", hi_root),
        ("alpha", alpha_derived), ("folded", folded), ("accepted", g(1)),
    ]
    .iter()
    .map(|(k, v)| ((*k).to_string(), *v))
    .collect();

    (inputs, root, seed)
}

#[test]
fn the_fold_challenge_is_derived_in_circuit_and_the_verifier_proves() {
    let (inputs, _root, _seed) = fs_query_inputs();
    let ir = Ir::from_json(VERIFIER_FS_IR).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
    )
    .unwrap();
    let vcircuit = lower_plonkish::<F>(&ir).unwrap();
    assert!(
        vcircuit.is_satisfied(&vcircuit.assignment(&wires)),
        "the verifier, deriving its own challenge, must accept the honest query"
    );

    let config = FriConfig::default();
    let outer = stark_prove::<F, CircuitHash>(&vcircuit, &wires, &config);
    assert!(
        stark_verify::<F, CircuitHash>(&vcircuit, &outer, &config).is_ok(),
        "the outer proof, with in-circuit Fiat-Shamir, must verify"
    );
}

#[test]
fn a_challenge_not_bound_to_the_commitment_is_rejected() {
    // The point of in-circuit Fiat-Shamir: alpha must equal fs_challenge(seed,
    // root). Supplying any other value fails the derivation constraint, so a
    // prover cannot pick a convenient challenge after committing.
    let (mut inputs, root, seed) = fs_query_inputs();
    let ir = Ir::from_json(VERIFIER_FS_IR).unwrap();
    let vcircuit = lower_plonkish::<F>(&ir).unwrap();

    // Swap in a different challenge (and keep everything else as computed).
    let honest_alpha = sbox(seed.add(root).add(g(6)));
    *inputs.get_mut("alpha").unwrap() = honest_alpha.add(F::one());

    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
    )
    .unwrap();
    assert!(
        !vcircuit.is_satisfied(&vcircuit.assignment(&wires)),
        "a challenge not derived from the commitment must be rejected"
    );
}
