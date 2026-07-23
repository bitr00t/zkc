//! Property tests for the NTT and LDE (phase 5, Workstream G.2).
//!
//! An FFT is pinned down by a few properties, and if they hold on random
//! inputs the transform is right: inverse-of-forward is the identity, the
//! forward transform agrees with naive polynomial evaluation on the subgroup,
//! and the roots of unity really have the claimed order. The LDE is pinned by
//! the one thing it must preserve — the underlying polynomial — so its
//! extended evaluations must match evaluating that polynomial directly.

use zkc_core::fft::{coset_lde, evaluate, intt, ntt};
use zkc_core::field::{TwoAdicField, ZkField};
use zkc_core::goldilocks::Goldilocks;

struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
}
fn g(v: u64) -> Goldilocks {
    Goldilocks::from_u64(v)
}
fn random_poly(rng: &mut Lcg, n: usize) -> Vec<Goldilocks> {
    (0..n).map(|_| g(rng.next_u64())).collect()
}

#[test]
fn two_adic_generators_have_the_claimed_order() {
    // g^(2^bits) = 1, and no smaller power of two is: g^(2^(bits-1)) = -1.
    for bits in 1..=12u32 {
        let root = Goldilocks::two_adic_generator(bits);
        // Order divides 2^bits.
        let mut acc = root;
        for _ in 0..bits {
            acc = ZkField::mul(acc, acc);
        }
        assert_eq!(acc, Goldilocks::one(), "g^(2^{bits}) != 1");
        // Primitive: the half-power is -1, not 1.
        let mut half = root;
        for _ in 0..(bits - 1) {
            half = ZkField::mul(half, half);
        }
        assert_eq!(half, ZkField::neg(Goldilocks::one()), "g is not primitive at 2^{bits}");
    }
}

#[test]
fn inverse_ntt_undoes_ntt() {
    let mut rng = Lcg(0xF17);
    for log_n in 0..=12u32 {
        let n = 1usize << log_n;
        let original = random_poly(&mut rng, n);
        let mut data = original.clone();
        ntt(&mut data);
        intt(&mut data);
        assert_eq!(data, original, "round-trip failed at n={n}");
    }
}

#[test]
fn ntt_agrees_with_naive_evaluation_on_the_subgroup() {
    // The forward NTT evaluates the coefficient polynomial at the powers of the
    // n-th root. Check that against Horner, point by point.
    let mut rng = Lcg(0xBEEF);
    for log_n in 1..=10u32 {
        let n = 1usize << log_n;
        let coefficients = random_poly(&mut rng, n);
        let mut evaluations = coefficients.clone();
        ntt(&mut evaluations);

        let root = Goldilocks::two_adic_generator(log_n);
        let mut point = Goldilocks::one();
        for evaluation in &evaluations {
            assert_eq!(*evaluation, evaluate(&coefficients, point), "NTT != naive eval at n={n}");
            point = ZkField::mul(point, root);
        }
    }
}

#[test]
fn coset_lde_preserves_the_polynomial() {
    // The LDE of n evaluations, on a coset of the n·blowup subgroup, must equal
    // evaluating the SAME polynomial at those coset points. That is the whole
    // contract: a redundant encoding, not a different function.
    let mut rng = Lcg(0xC05E7);
    for log_n in 1..=8u32 {
        let n = 1usize << log_n;
        let blowup = 4;
        let coefficients = random_poly(&mut rng, n);

        // Evaluations on the subgroup are what coset_lde takes as input.
        let mut subgroup_evals = coefficients.clone();
        ntt(&mut subgroup_evals);

        let shift = g(7); // any nonzero non-root works as a coset shift
        let extended = coset_lde(&subgroup_evals, blowup, shift);
        assert_eq!(extended.len(), n * blowup);

        // Ground truth: evaluate the polynomial at shift · ω^i on the big
        // subgroup.
        let big = n * blowup;
        let big_root = Goldilocks::two_adic_generator(big.trailing_zeros());
        let mut point = shift;
        for expected_at in &extended {
            assert_eq!(*expected_at, evaluate(&coefficients, point), "LDE mismatch at n={n}");
            point = ZkField::mul(point, big_root);
        }
    }
}

#[test]
fn ntt_handles_the_degenerate_sizes() {
    // n = 1 is identity; the transform must not panic or scale.
    let mut one = vec![g(42)];
    ntt(&mut one);
    assert_eq!(one, vec![g(42)]);
    intt(&mut one);
    assert_eq!(one, vec![g(42)]);
}
