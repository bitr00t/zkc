//! The field abstraction.
//!
//! Everything in this crate — witness solving, lowering, checking — is
//! generic over [`ZkField`] rather than tied to one concrete field. That is
//! a deliberate architectural invariant, not ceremony:
//!
//!   * R1CS + Groth16 (phases 1-3) wants a ~254-bit pairing-friendly field
//!     such as BN254's scalar field;
//!   * FRI/STARK (phase 5) wants a *small* field with high two-adicity such
//!     as Goldilocks (`2^64 - 2^32 + 1`), where a 254-bit field would be a
//!     performance disaster.
//!
//! A blanket impl covers every arkworks `PrimeField`, so today's backend
//! works out of the box; phase 5's hand-rolled field only has to implement
//! this trait for the rest of the compiler to keep working unchanged.

use ark_ff::PrimeField;

pub trait ZkField: Copy + PartialEq + core::fmt::Debug {
    fn zero() -> Self;
    fn one() -> Self;
    fn add(self, other: Self) -> Self;
    fn sub(self, other: Self) -> Self;
    fn mul(self, other: Self) -> Self;
    fn neg(self) -> Self;
    fn inverse(self) -> Option<Self>;

    fn is_zero(self) -> bool {
        self == Self::zero()
    }

    /// Parse a decimal string, which may carry a leading `-`.
    ///
    /// The IR encodes constants as decimal *strings* because field elements
    /// routinely exceed 64 bits and JSON numbers cannot represent them
    /// safely. Parsing is Horner's method, so arbitrary lengths work.
    fn from_decimal(text: &str) -> Result<Self, String> {
        let (negative, digits) = match text.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, text),
        };
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return Err(format!("not a decimal integer: {text:?}"));
        }
        let ten = Self::from_u64(10);
        let mut accumulator = Self::zero();
        for byte in digits.bytes() {
            accumulator = accumulator.mul(ten).add(Self::from_u64(u64::from(byte - b'0')));
        }
        Ok(if negative { accumulator.neg() } else { accumulator })
    }

    fn from_u64(value: u64) -> Self;

    /// Canonical decimal representation.
    fn to_decimal(self) -> String;
}

/// A field with a large power-of-two multiplicative subgroup.
///
/// FFT — and therefore FRI, and therefore the phase-5 prover — needs a
/// primitive `2^k`-th root of unity to build an evaluation domain of size
/// `2^k`. Not every field has one: Goldilocks does (`2^32 | p - 1`), a
/// 254-bit pairing field essentially does not, which is the whole reason the
/// two phases use different fields. This extension trait is what the FFT is
/// written against, so the FFT never names a concrete field either.
pub trait TwoAdicField: ZkField {
    /// The largest `k` with a primitive `2^k`-th root of unity.
    const TWO_ADICITY: u32;

    /// A primitive `2^bits`-th root of unity. Requires `bits <= TWO_ADICITY`.
    fn two_adic_generator(bits: u32) -> Self;
}

impl<F: PrimeField> ZkField for F {
    fn zero() -> Self {
        <F as ark_ff::Zero>::zero()
    }
    fn one() -> Self {
        <F as ark_ff::One>::one()
    }
    fn add(self, other: Self) -> Self {
        self + other
    }
    fn sub(self, other: Self) -> Self {
        self - other
    }
    fn mul(self, other: Self) -> Self {
        self * other
    }
    fn neg(self) -> Self {
        -self
    }
    fn inverse(self) -> Option<Self> {
        ark_ff::Field::inverse(&self)
    }
    fn from_u64(value: u64) -> Self {
        // Fully qualified on purpose. Inside this blanket impl `F::from` has
        // two candidates: `From<u64> for F` (via arkworks' `Field`) and the
        // reflexive `impl<T> From<T> for T`. rustc disambiguates them from the
        // argument type, but the ambiguity is real and rust-analyzer resolves
        // it the other way, reporting a phantom "expected F, found u64".
        // Naming the impl costs nothing and matches how `zero`, `one` and
        // `inverse` above avoid recursing into this very trait.
        <F as From<u64>>::from(value)
    }
    fn to_decimal(self) -> String {
        self.into_bigint().to_string()
    }
}