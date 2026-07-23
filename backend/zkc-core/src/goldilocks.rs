//! The Goldilocks field, `p = 2^64 - 2^32 + 1`, hand-written.
//!
//! Phases 1–4 borrow a field (BN254's scalar field, via arkworks) because they
//! borrow a prover: Groth16 wants a ~254-bit pairing-friendly field. Phase 5
//! writes its own FRI/STARK prover, and a STARK wants the opposite — a *small*
//! field with high two-adicity, so its FFTs are cheap. This is that field, and
//! the point of writing it by hand is the same as the point of the whole
//! roadmap: own language, own arithmetization, own prover, own field.
//!
//! ## Why this prime
//!
//! Two properties earn Goldilocks its place.
//!
//! It **fits in a machine word.** Every element is a `u64 < p`, so arithmetic
//! is register-width and multiplication is a single `u64 * u64 -> u128`.
//!
//! Its **multiplicative group is highly two-adic:** `p - 1 = 2^32 · 3 · 5 · 17
//! · 257 · 65537`, divisible by `2^32`. FFT needs a primitive `2^k`-th root of
//! unity to build an evaluation domain of size `2^k`; the factor of `2^32`
//! means domains up to `2^32 ≈ 4 billion` rows exist. A 254-bit field has no
//! such structure and would make FRI's FFTs a performance disaster — which is
//! exactly the trade the two fields represent.
//!
//! ## Why the reduction is fast
//!
//! The whole speed argument rests on the shape of `p`. Because
//! `2^64 ≡ 2^32 - 1 (mod p)`, a 128-bit product `hi · 2^64 + lo` reduces with
//! a couple of word operations and no general division — see [`reduce128`].
//! That is the one piece of cleverness here; everything else is schoolbook.
//!
//! ## Trust
//!
//! Correctness is not asserted, it is *differentially tested*: every operation
//! is checked against an independent Goldilocks (arkworks' `Fp64`) on random
//! inputs, the same discipline phase 4 used to trust its second arithmetization.
//! The reference lives only in the test build; nothing here depends on it.

use crate::field::{TwoAdicField, ZkField};

/// The Goldilocks prime, `2^64 - 2^32 + 1`.
pub const MODULUS: u64 = 0xFFFF_FFFF_0000_0001;

/// `2^64 mod p = 2^32 - 1`. The constant that makes reduction cheap.
const EPSILON: u64 = 0xFFFF_FFFF; // 2^32 - 1

/// An element of the Goldilocks field, always stored reduced (`0 <= value < p`).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Goldilocks(u64);

impl core::fmt::Debug for Goldilocks {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Goldilocks({})", self.0)
    }
}

impl Goldilocks {
    /// Reduce an arbitrary `u64` (which may be `>= p`) into canonical form.
    #[inline]
    pub const fn from_canonical_u64(value: u64) -> Self {
        Goldilocks(if value >= MODULUS { value - MODULUS } else { value })
    }

    /// The raw representative, in `[0, p)`.
    #[inline]
    pub const fn as_u64(self) -> u64 {
        self.0
    }

    /// Reduce a 128-bit value modulo `p`, cheaply.
    ///
    /// Write `x = hi · 2^64 + lo`. Since `2^64 ≡ 2^32 - 1`, we have
    /// `x ≡ lo + hi · (2^32 - 1) = lo + hi · 2^32 - hi`. Split `hi` itself into
    /// its low and high halves so `hi · 2^32` also stays analysable:
    /// `hi = hi_hi · 2^32 + hi_lo`, and `hi_hi · 2^64 ≡ hi_hi · (2^32 - 1)`
    /// again, which for `hi_hi < 2^32` is just `hi_hi · 2^32 - hi_hi` and folds
    /// into a second, smaller correction. The result needs at most two
    /// conditional subtractions of `p`. This is the standard Goldilocks
    /// reduction; the borrows are handled explicitly so the logic is visible.
    #[inline]
    pub fn reduce128(x: u128) -> Self {
        let lo = x as u64;
        let hi = (x >> 64) as u64;
        let hi_hi = hi >> 32;
        let hi_lo = hi & 0xFFFF_FFFF;

        // t0 = lo - hi_hi, borrowing a p if it underflows.
        let (mut t0, borrow) = lo.overflowing_sub(hi_hi);
        if borrow {
            t0 = t0.wrapping_sub(EPSILON); // subtracting p, whose low word folds to +EPSILON here
        }
        // t1 = hi_lo · (2^32 - 1), which fits in 64 bits and needs its own reduce.
        let t1 = hi_lo
            .wrapping_mul(EPSILON);
        // Sum t0 + t1 modulo p, with a carry correction.
        let (sum, carry) = t0.overflowing_add(t1);
        let mut result = sum;
        if carry {
            result = result.wrapping_add(EPSILON);
        }
        Self::from_canonical_u64(result)
    }

    /// `self^exponent`, by square-and-multiply. Used for inversion and roots.
    pub fn pow(self, mut exponent: u64) -> Self {
        let mut base = self;
        let mut acc = Goldilocks(1 % MODULUS);
        while exponent > 0 {
            if exponent & 1 == 1 {
                acc = ZkField::mul(acc, base);
            }
            base = ZkField::mul(base, base);
            exponent >>= 1;
        }
        acc
    }
}

impl ZkField for Goldilocks {
    #[inline]
    fn zero() -> Self {
        Goldilocks(0)
    }
    #[inline]
    fn one() -> Self {
        Goldilocks(1)
    }

    #[inline]
    fn add(self, other: Self) -> Self {
        // a + b may overflow 64 bits; the overflow is one p, corrected by
        // adding EPSILON (since 2^64 ≡ 2^32 - 1) and reducing once.
        let (sum, carry) = self.0.overflowing_add(other.0);
        let mut result = sum;
        if carry {
            result = result.wrapping_add(EPSILON);
        }
        Self::from_canonical_u64(result)
    }

    #[inline]
    fn sub(self, other: Self) -> Self {
        // a - b borrows one p on underflow; borrowing p subtracts EPSILON from
        // the low word.
        let (diff, borrow) = self.0.overflowing_sub(other.0);
        let mut result = diff;
        if borrow {
            result = result.wrapping_sub(EPSILON);
        }
        Self::from_canonical_u64(result)
    }

    #[inline]
    fn mul(self, other: Self) -> Self {
        Self::reduce128((self.0 as u128) * (other.0 as u128))
    }

    #[inline]
    fn neg(self) -> Self {
        if self.0 == 0 {
            self
        } else {
            Goldilocks(MODULUS - self.0)
        }
    }

    fn inverse(self) -> Option<Self> {
        if self.0 == 0 {
            return None;
        }
        // Fermat: a^(p-2) = a^{-1}. No extended-Euclid needed, and constant in
        // control flow, which is a virtue for a field element.
        Some(self.pow(MODULUS - 2))
    }

    #[inline]
    fn from_u64(value: u64) -> Self {
        Self::from_canonical_u64(value)
    }

    fn to_decimal(self) -> String {
        self.0.to_string()
    }
}

impl TwoAdicField for Goldilocks {
    // p - 1 = 2^32 · (odd), so domains up to 2^32 exist.
    const TWO_ADICITY: u32 = 32;

    fn two_adic_generator(bits: u32) -> Self {
        assert!(
            bits <= Self::TWO_ADICITY,
            "no 2^{bits} root of unity: Goldilocks is 2-adic only up to 2^{}",
            Self::TWO_ADICITY
        );
        // A known generator of the full 2^32 subgroup, then squared down to the
        // subgroup of size 2^bits. 7 is a multiplicative generator of the whole
        // field; g^((p-1)/2^32) generates the 2^32-torsion.
        //
        // (p - 1) / 2^32 = 0xFFFF_FFFF, the odd cofactor.
        let full = Goldilocks::from_canonical_u64(7).pow(0xFFFF_FFFF);
        // Square (2^32 - bits) times to land in the size-2^bits subgroup.
        let mut generator = full;
        for _ in 0..(Self::TWO_ADICITY - bits) {
            generator = ZkField::mul(generator, generator);
        }
        generator
    }
}