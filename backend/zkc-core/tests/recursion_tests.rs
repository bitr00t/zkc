//! Phase 7, O.2 — recursive composition: one proof attesting to another.
//!
//! The smallest honest recursion. An inner FRI proof of a low-degree polynomial
//! is produced and verified. From it we pull one *real* fold step — the openings
//! f(x) and f(-x), the transcript's folding challenge, the domain point, and the
//! next-layer value the proof claims — and hand them to the `fri_fold` verifier
//! circuit (O.1). Proving *that* circuit with the same STARK prover is the
//! recursion: an outer proof attesting that the inner proof's fold relation
//! holds. Tampering the claimed value breaks the outer proof, exactly as the
//! phase-0 forgery broke the very first one.

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

#[derive(Clone)]
struct ToyHash;
fn g(v: u64) -> F {
    F::from_u64(v)
}
fn sbox(x: F) -> F {
    let x2 = x.mul(x);
    let x4 = x2.mul(x2);
    x4.mul(x2).mul(x)
}
impl Hasher<F> for ToyHash {
    const WIDTH: usize = 1;
    fn hash(input: &[F]) -> Digest<F> {
        let mut s = g(0x9E3779B97F4A7C15);
        for (i, x) in input.iter().enumerate() {
            s = sbox(s.add(x.add(g(i as u64 + 1))));
        }
        Digest(vec![sbox(s)])
    }
    fn compress(l: &Digest<F>, r: &Digest<F>) -> Digest<F> {
        Self::hash(&[l.0[0], r.0[0]])
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

// The verifier check, compiled from std/fri_fold.zkc (phase 7, O.1).
const FRI_FOLD_IR: &str = r#"{"schema_version":2,"name":"FriFold","field":"bn254","const_one_wire":0,"inputs":[{"wire":1,"name":"p","visibility":"private","line":2},{"wire":2,"name":"m","visibility":"private","line":2},{"wire":3,"name":"beta","visibility":"private","line":2},{"wire":4,"name":"x","visibility":"private","line":2},{"wire":5,"name":"o","visibility":"output","line":2}],"nodes":[{"wire":6,"advice_derived":false,"line":16,"op":"add","args":[4,4]},{"wire":7,"advice_derived":true,"op":"hint","hint":"inv","name":"inv2x","gadget":"fri_fold","line":16,"args":[6]},{"wire":8,"advice_derived":true,"line":17,"op":"mul","args":[6,7]},{"wire":9,"advice_derived":false,"line":17,"op":"const","value":"1"},{"wire":10,"advice_derived":false,"line":18,"op":"add","args":[1,2]},{"wire":11,"advice_derived":false,"line":18,"op":"mul","args":[4,10]},{"wire":12,"advice_derived":false,"line":18,"op":"sub","args":[1,2]},{"wire":13,"advice_derived":false,"line":18,"op":"mul","args":[3,12]},{"wire":14,"advice_derived":false,"line":18,"op":"add","args":[11,13]},{"wire":15,"advice_derived":true,"line":19,"op":"mul","args":[7,14]}],"assertions":[{"lhs":8,"rhs":9,"label":"((x + x) * inv2x) == 1","line":17},{"lhs":5,"rhs":15,"label":"folded == (inv2x * rhs)","line":19}],"determinacy":{"proved":true,"targets":["o"],"branches":[["x == 0"],["x != 0"]]}}"#;

/// A real inner FRI proof plus one fold step drawn from it:
/// (p = f(x), m = f(-x), beta, x, claimed_next).
fn inner_proof_and_fold_step() -> (F, F, F, F, F) {
    let degree_bound = 8usize;
    let config = FriConfig::default();
    let coeffs: Vec<F> = [3u64, 1, 4, 1, 5, 9, 2, 6].iter().map(|&v| g(v)).collect();

    // Inner proof, and it must verify — this is the proof we recurse over.
    let mut prover_t = Transcript::<_, ToyHash>::new(&[g(1)]);
    let inner = fri_prove(&coeffs, degree_bound, &config, &mut prover_t);
    let mut verifier_t = Transcript::<_, ToyHash>::new(&[g(1)]);
    assert!(
        fri_verify(&inner, degree_bound, &config, &mut verifier_t).is_ok(),
        "the inner FRI proof must verify"
    );

    // Replay the transcript for the folding challenges, exactly as verify does.
    let mut replay = Transcript::<_, ToyHash>::new(&[g(1)]);
    let mut alphas = Vec::new();
    for root in &inner.roots {
        replay.absorb_digest(root);
        alphas.push(replay.challenge());
    }

    // Query 0, round 0: the openings, the domain point, and the value the proof
    // claims for the next layer at the carried position.
    let domain_size = inner.domain_size;
    let shift = coset_shift::<F>();
    let query = &inner.queries[0];
    let half0 = domain_size / 2;
    let lo0 = query.index % half0;
    let gen0 = F::two_adic_generator(domain_size.trailing_zeros());
    let x = shift.mul(pow(gen0, lo0 as u64));
    let p = query.layers[0].lo;
    let m = query.layers[0].hi;
    let beta = alphas[0];
    let half1 = half0 / 2;
    let claimed_next = if lo0 < half1 {
        query.layers[1].lo
    } else {
        query.layers[1].hi
    };
    (p, m, beta, x, claimed_next)
}

fn fold_witness(p: F, m: F, beta: F, x: F, o: F) -> (Ir, Vec<F>) {
    let ir = Ir::from_json(FRI_FOLD_IR).unwrap();
    let inputs: HashMap<String, F> = [("p", p), ("m", m), ("beta", beta), ("x", x), ("o", o)]
        .iter()
        .map(|(k, v)| ((*k).to_string(), *v))
        .collect();
    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
    )
    .unwrap();
    (ir, wires)
}

#[test]
fn a_real_fri_fold_is_verified_inside_an_outer_proof() {
    let (p, m, beta, x, claimed_next) = inner_proof_and_fold_step();
    let config = FriConfig::default();

    // The verifier circuit, handed the real fold step, must be satisfied...
    let (_ir, wires) = fold_witness(p, m, beta, x, claimed_next);
    let vcircuit = lower_plonkish::<F>(&Ir::from_json(FRI_FOLD_IR).unwrap()).unwrap();
    assert!(
        vcircuit.is_satisfied(&vcircuit.assignment(&wires)),
        "the verifier circuit must accept the inner proof's real fold"
    );

    // ...and proving it produces an outer proof that verifies. The recursion.
    let outer = stark_prove::<F, ToyHash>(&vcircuit, &wires, &config);
    assert!(
        stark_verify::<F, ToyHash>(&vcircuit, &outer, &config).is_ok(),
        "the outer proof — attesting the inner fold — must verify"
    );
}

#[test]
fn a_tampered_inner_claim_breaks_the_outer_proof() {
    let (p, m, beta, x, claimed_next) = inner_proof_and_fold_step();
    let config = FriConfig::default();
    let vcircuit = lower_plonkish::<F>(&Ir::from_json(FRI_FOLD_IR).unwrap()).unwrap();

    // Tamper the value the inner proof claims for the next layer.
    let (_ir, bad_wires) = fold_witness(p, m, beta, x, claimed_next.add(F::one()));

    // An honest prover refuses: the verifier circuit is not satisfied.
    assert!(
        !vcircuit.is_satisfied(&vcircuit.assignment(&bad_wires)),
        "a tampered fold claim must be rejected before proving"
    );

    // And a maliciously forced outer proof does not verify.
    let forced = stark_prove::<F, ToyHash>(&vcircuit, &bad_wires, &config);
    assert!(
        stark_verify::<F, ToyHash>(&vcircuit, &forced, &config).is_err(),
        "a forged outer proof must not verify"
    );
}