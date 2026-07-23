//! Differential + property tests for the hand-written Goldilocks field
//! (phase 5, Workstream G.1).
//!
//! Nothing here is asserted correct; it is checked against an INDEPENDENT
//! Goldilocks — arkworks' `Fp64` with the same modulus — on random inputs.
//! Every operation the field claims must agree with the reference, and the
//! reduction, which is the one clever line, gets the hardest inputs (values
//! near the modulus, products near `2^128`). The reference exists only in this
//! test binary.

use ark_ff::{Fp64, MontBackend, MontConfig, PrimeField, Field, Zero, One};

/// A tiny deterministic LCG — no extra dependency, reproducible on failure.
struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn range(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

use zkc_core::field::{TwoAdicField, ZkField};
use zkc_core::goldilocks::{Goldilocks, MODULUS};

#[derive(MontConfig)]
#[modulus = "18446744069414584321"] // 2^64 - 2^32 + 1
#[generator = "7"]
struct RefConfig;
type Reference = Fp64<MontBackend<RefConfig, 1>>;

fn to_ref(x: Goldilocks) -> Reference {
    Reference::from(x.as_u64())
}
fn ref_to_u64(x: Reference) -> u64 {
    // canonical little-endian; the value is < 2^64 so the first limb is it.
    x.into_bigint().0[0]
}

fn rng() -> Lcg {
    Lcg(0x0F1E1DC0DE)
}

/// A random field element, biased toward the hard cases: values near 0 and
/// near p, where borrows and carries actually happen.
fn sample(rng: &mut Lcg) -> Goldilocks {
    match rng.range(5) {
        0 => Goldilocks::from_canonical_u64(0),
        1 => Goldilocks::from_canonical_u64(MODULUS - 1),
        2 => Goldilocks::from_canonical_u64(rng.range(16)),
        3 => Goldilocks::from_canonical_u64(MODULUS - 1 - rng.range(16)),
        _ => Goldilocks::from_u64(rng.next_u64()), // any u64, reduced
    }
}

#[test]
fn add_sub_mul_neg_agree_with_the_reference() {
    let mut rng = rng();
    for _ in 0..50_000 {
        let a = sample(&mut rng);
        let b = sample(&mut rng);
        let (ra, rb) = (to_ref(a), to_ref(b));

        assert_eq!(ZkField::add(a, b).as_u64(), ref_to_u64(ra + rb), "add {a:?} {b:?}");
        assert_eq!(ZkField::sub(a, b).as_u64(), ref_to_u64(ra - rb), "sub {a:?} {b:?}");
        assert_eq!(ZkField::mul(a, b).as_u64(), ref_to_u64(ra * rb), "mul {a:?} {b:?}");
        assert_eq!(ZkField::neg(a).as_u64(), ref_to_u64(-ra), "neg {a:?}");
    }
}

#[test]
fn inverse_agrees_and_zero_has_none() {
    let mut rng = rng();
    assert!(ZkField::inverse(Goldilocks::zero()).is_none(), "zero must not be invertible");
    for _ in 0..20_000 {
        let a = sample(&mut rng);
        if a == Goldilocks::zero() {
            continue;
        }
        let inv = ZkField::inverse(a).expect("nonzero is invertible");
        // a · a^{-1} = 1, and it matches the reference inverse.
        assert_eq!(ZkField::mul(a, inv), Goldilocks::one(), "a·a⁻¹ ≠ 1 for {a:?}");
        assert_eq!(inv.as_u64(), ref_to_u64(to_ref(a).inverse().unwrap()), "inverse {a:?}");
    }
}

#[test]
fn the_reduction_survives_the_worst_products() {
    // (p-1)² is the largest product two field elements can form, and the place
    // a reduction bug hides. Hammer the top of the range specifically.
    let mut rng = rng();
    for _ in 0..50_000 {
        let a = Goldilocks::from_canonical_u64(MODULUS - 1 - rng.range(1 << 20));
        let b = Goldilocks::from_canonical_u64(MODULUS - 1 - rng.range(1 << 20));
        assert_eq!(
            ZkField::mul(a, b).as_u64(),
            ref_to_u64(to_ref(a) * to_ref(b)),
            "mul near p: {a:?} {b:?}"
        );
    }
    // The exact corner: (p-1)².
    let pm1 = Goldilocks::from_canonical_u64(MODULUS - 1);
    assert_eq!(ZkField::mul(pm1, pm1).as_u64(), ref_to_u64(to_ref(pm1) * to_ref(pm1)));
}

#[test]
fn decimal_round_trips() {
    let mut rng = rng();
    for _ in 0..10_000 {
        let a = sample(&mut rng);
        let text = a.to_decimal();
        let back = Goldilocks::from_decimal(&text).unwrap();
        assert_eq!(a, back, "decimal round-trip failed for {a:?}");
    }
    // Negative decimals (the IR uses them) land in the field correctly.
    assert_eq!(Goldilocks::from_decimal("-1").unwrap(), ZkField::neg(Goldilocks::one()));
}

#[test]
fn field_axioms_hold() {
    let mut rng = rng();
    for _ in 0..10_000 {
        let a = sample(&mut rng);
        let b = sample(&mut rng);
        let c = sample(&mut rng);
        // commutativity, associativity, distributivity, identities.
        assert_eq!(ZkField::add(a, b), ZkField::add(b, a));
        assert_eq!(ZkField::mul(a, b), ZkField::mul(b, a));
        assert_eq!(ZkField::add(ZkField::add(a, b), c), ZkField::add(a, ZkField::add(b, c)));
        assert_eq!(ZkField::mul(ZkField::mul(a, b), c), ZkField::mul(a, ZkField::mul(b, c)));
        assert_eq!(
            ZkField::mul(a, ZkField::add(b, c)),
            ZkField::add(ZkField::mul(a, b), ZkField::mul(a, c))
        );
        assert_eq!(ZkField::add(a, Goldilocks::zero()), a);
        assert_eq!(ZkField::mul(a, Goldilocks::one()), a);
        assert_eq!(ZkField::add(a, ZkField::neg(a)), Goldilocks::zero());
    }
}
