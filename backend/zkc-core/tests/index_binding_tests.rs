//! Phase 7, O — the query index, and the boundary of what determinacy proves.
//!
//! In-circuit Fiat-Shamir derived the fold challenge (see fri_verifier_tests).
//! The query index is the other Fiat-Shamir value. The backend now derives it
//! as an honest algebraic reduction — `challenge mod domain`, the low bits of
//! the canonical representative — which is the value an in-circuit derivation
//! would have to reproduce. This file records both that fact and *why* the
//! in-circuit derivation cannot yet be done soundly: the natural binding proves
//! determinate but is unsound, and closing the gap needs a decomposition hint
//! the language does not provide.

use std::collections::HashMap;

use zkc_core::field::ZkField;
use zkc_core::goldilocks::Goldilocks;
use zkc_core::hash::{Digest, Hasher};
use zkc_core::ir::Ir;
use zkc_core::transcript::Transcript;
use zkc_core::witness::{solve, SolveInputs};

type F = Goldilocks;
fn g(v: u64) -> F {
    F::from_u64(v)
}
fn sbox(x: F) -> F {
    let x2 = x.mul(x);
    x2.mul(x2).mul(x2).mul(x)
}
#[derive(Clone)]
struct H;
impl Hasher<F> for H {
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

/// The canonical reduction the in-circuit derivation would target.
fn value_mod(value: F, domain: usize) -> usize {
    value
        .to_decimal()
        .bytes()
        .fold(0usize, |acc, b| (acc * 10 + (b - b'0') as usize) % domain)
}

#[test]
fn the_query_index_is_an_algebraic_reduction_of_the_challenge() {
    // Two identical transcripts: one draws the index, the other the raw
    // challenge. The index must be exactly .
    let domain = 64usize;
    let mut t_index = Transcript::<_, H>::new(&[g(9)]);
    t_index.absorb(&[g(1), g(2), g(3)]);
    let mut t_raw = Transcript::<_, H>::new(&[g(9)]);
    t_raw.absorb(&[g(1), g(2), g(3)]);

    for _ in 0..64 {
        let idx = t_index.challenge_index(domain);
        let raw = t_raw.challenge();
        assert!(idx < domain);
        assert_eq!(idx, value_mod(raw, domain), "the index is challenge mod domain");
    }
}

// The naive in-circuit binding, compiled from examples/index_from_challenge.zkc.
const INDEX_BINDING_IR: &str = include_str!("fixtures/index_from_challenge.ir.json");

#[test]
fn naive_index_binding_is_determinate_but_unsound() {
    // The frontend PROVES this circuit determinate —  is a function of its
    // inputs. Yet every index in {0,1,2,3} satisfies it: the prover picks
    // high = (challenge - index)/4 to hit any index it likes. Determinacy rules
    // out under-constrained *outputs*; it does not, and cannot, certify that an
    // output equals a canonical reduction. That is a range property, and needs a
    // bounded decomposition the language cannot yet express.
    let ir = Ir::from_json(INDEX_BINDING_IR).unwrap();
    let challenge = g(0x0123_4567_89ab_cdef);
    let inv4 = g(4).inverse().unwrap();

    let mut satisfying = Vec::new();
    for index in 0u64..4 {
        let idx_f = g(index);
        let high = challenge.sub(idx_f).mul(inv4); // always solvable — the hole
        let inputs: HashMap<String, F> = [
            ("challenge", challenge),
            ("b0", g(index & 1)),
            ("b1", g((index >> 1) & 1)),
            ("high", high),
            ("idx", idx_f),
        ]
        .iter()
        .map(|(k, v)| ((*k).to_string(), *v))
        .collect();
        let wires = solve::<F>(
            &ir,
            &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
        )
        .unwrap();
        if ir.is_satisfied::<F>(&wires) {
            satisfying.push(index);
        }
    }

    assert_eq!(
        satisfying,
        vec![0, 1, 2, 3],
        "every index satisfies the naive binding — it is determinate but unsound"
    );
}