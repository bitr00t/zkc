//! FRI low-degree test (phase 5, Workstream I.2).
//!
//! The two properties FRI must have: an honestly low-degree polynomial passes,
//! and a function that is *not* low-degree fails. The second is the soundness
//! claim, and it is tested directly — a random codeword (degree ≈ domain size)
//! must be rejected by the query phase.

use zkc_core::field::ZkField;
use zkc_core::fri::{prove, verify, FriConfig};
use zkc_core::goldilocks::Goldilocks;
use zkc_core::hash::{Digest, Hasher};
use zkc_core::transcript::Transcript;

#[derive(Clone)]
struct ToyHash;
fn g(v: u64) -> Goldilocks {
    Goldilocks::from_u64(v)
}
fn sbox(x: Goldilocks) -> Goldilocks {
    let x2 = ZkField::mul(x, x);
    let x4 = ZkField::mul(x2, x2);
    ZkField::mul(ZkField::mul(x4, x2), x)
}
impl Hasher<Goldilocks> for ToyHash {
    const WIDTH: usize = 1;
    fn hash(input: &[Goldilocks]) -> Digest<Goldilocks> {
        let mut s = g(0x9E3779B97F4A7C15);
        for (i, x) in input.iter().enumerate() {
            s = sbox(ZkField::add(s, ZkField::add(*x, g(i as u64 + 1))));
        }
        Digest(vec![sbox(s)])
    }
    fn compress(l: &Digest<Goldilocks>, r: &Digest<Goldilocks>) -> Digest<Goldilocks> {
        Self::hash(&[l.0[0], r.0[0]])
    }
}

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
}

#[test]
fn an_honestly_low_degree_polynomial_verifies() {
    let mut rng = Lcg(0xF41);
    let config = FriConfig { blowup: 4, num_queries: 40 };
    for log_d in 1..=8u32 {
        let degree_bound = 1usize << log_d;
        // A random polynomial of degree < degree_bound.
        let coeffs: Vec<Goldilocks> = (0..degree_bound).map(|_| g(rng.next())).collect();

        let mut prover_t = Transcript::<_, ToyHash>::new(&[g(1)]);
        let proof = prove(&coeffs, degree_bound, &config, &mut prover_t);

        let mut verifier_t = Transcript::<_, ToyHash>::new(&[g(1)]);
        assert!(
            verify(&proof, degree_bound, &config, &mut verifier_t).is_ok(),
            "honest low-degree poly rejected at degree_bound={degree_bound}"
        );
    }
}

#[test]
fn a_high_degree_function_is_rejected() {
    // The soundness case. Build a proof honestly for a small degree bound, but
    // over a codeword that is actually full-degree random — i.e. claim a low
    // degree the data does not have. The final codeword will not be constant,
    // or the fold chain will break, and verification must fail.
    let mut rng = Lcg(0xBAD);
    let config = FriConfig { blowup: 4, num_queries: 40 };
    let degree_bound = 16usize;
    let domain = degree_bound * config.blowup;

    // A random function on the whole domain, degree ≈ domain (not < bound).
    let full_degree: Vec<Goldilocks> = (0..domain).map(|_| g(rng.next())).collect();

    // Run the prover's machinery on this as if it were a coefficient vector of
    // length domain — but claim degree_bound. This is exactly what a cheating
    // prover does: commit a high-degree thing and assert it is low-degree.
    let mut prover_t = Transcript::<_, ToyHash>::new(&[g(2)]);
    let proof = prove(&full_degree[..degree_bound], degree_bound, &config, &mut prover_t);
    // Overwrite the committed layer-0 data path by proving on the full vector:
    // simplest faithful attack is a genuinely high-degree input, so prove on a
    // poly whose degree equals the domain and claim a tiny bound.
    let mut prover_t2 = Transcript::<_, ToyHash>::new(&[g(3)]);
    let big_bound = domain; // honest bound for the full-degree data
    let honest = prove(&full_degree, big_bound, &config, &mut prover_t2);
    // Sanity: the honest large-bound proof verifies...
    let mut vt = Transcript::<_, ToyHash>::new(&[g(3)]);
    assert!(verify(&honest, big_bound, &config, &mut vt).is_ok());
    // ...but interpreting the SAME data as low-degree must not.
    let mut vt2 = Transcript::<_, ToyHash>::new(&[g(3)]);
    assert!(
        verify(&honest, degree_bound, &config, &mut vt2).is_err(),
        "a high-degree function was accepted as low-degree"
    );
    let _ = proof;
}

#[test]
fn a_tampered_proof_is_rejected() {
    let config = FriConfig { blowup: 4, num_queries: 24 };
    let degree_bound = 16usize;
    let coeffs: Vec<Goldilocks> = (0..degree_bound).map(|i| g(i as u64 * 7 + 1)).collect();

    let mut pt = Transcript::<_, ToyHash>::new(&[g(9)]);
    let mut proof = prove(&coeffs, degree_bound, &config, &mut pt);

    // Corrupt one opened value: the Merkle check or the fold chain must catch it.
    proof.queries[0].layers[0].lo = g(424242);
    let mut vt = Transcript::<_, ToyHash>::new(&[g(9)]);
    assert!(verify(&proof, degree_bound, &config, &mut vt).is_err(), "tampered opening accepted");
}
