//! Number-theoretic transform and low-degree extension (phase 5, G.2).
//!
//! FRI is built on the FFT, and the FFT over a finite field is the
//! number-theoretic transform: the same Cooley–Tukey butterflies, with a
//! primitive `2^k`-th root of unity in place of `e^{2πi/n}`. That root is what
//! [`TwoAdicField`] provides and what a 254-bit pairing field cannot, which is
//! the whole reason phase 5 changes fields.
//!
//! Three operations, each a thin layer on the last:
//!
//!   * [`ntt`] / [`intt`] — evaluate a polynomial (given by coefficients) on
//!     the size-`n` multiplicative subgroup, and invert;
//!   * [`coset_lde`] — the low-degree extension FRI actually commits to:
//!     interpolate `n` values, then evaluate the same polynomial on a larger
//!     coset.
//!
//! Everything is generic over [`TwoAdicField`]; nothing here names Goldilocks.
//! Correctness is pinned by the properties that define an FFT — round-trip,
//! and agreement with naive evaluation — not by inspection.

use crate::field::{TwoAdicField, ZkField};

/// The forward NTT, in place. `values` holds polynomial coefficients on entry
/// and its evaluations on the size-`n` subgroup on exit. `n` must be a power
/// of two.
pub fn ntt<F: TwoAdicField>(values: &mut [F]) {
    let n = values.len();
    assert!(n.is_power_of_two(), "NTT length must be a power of two, got {n}");
    if n <= 1 {
        return;
    }
    let bits = n.trailing_zeros();
    let root = F::two_adic_generator(bits);
    transform(values, root);
}

/// The inverse NTT: evaluations back to coefficients. Scales by `n^{-1}`.
pub fn intt<F: TwoAdicField>(values: &mut [F]) {
    let n = values.len();
    assert!(n.is_power_of_two(), "iNTT length must be a power of two, got {n}");
    if n <= 1 {
        return;
    }
    let bits = n.trailing_zeros();
    let root = F::two_adic_generator(bits);
    let inverse_root = root.inverse().expect("a root of unity is nonzero");
    transform(values, inverse_root);
    let n_inverse = F::from_u64(n as u64).inverse().expect("n is nonzero in a large field");
    for value in values.iter_mut() {
        *value = value.mul(n_inverse);
    }
}

/// Iterative Cooley–Tukey with a given primitive `n`-th root. Decimation in
/// time: bit-reverse, then `log n` layers of butterflies.
fn transform<F: ZkField>(values: &mut [F], root: F) {
    let n = values.len();
    bit_reverse_permute(values);

    let mut length = 2;
    while length <= n {
        // `w` is a primitive `length`-th root: root^(n/length).
        let step = n / length;
        let w_length = pow(root, step as u64);
        let half = length / 2;
        let mut start = 0;
        while start < n {
            let mut w = F::one();
            for offset in 0..half {
                let a = values[start + offset];
                let b = values[start + offset + half].mul(w);
                values[start + offset] = a.add(b);
                values[start + offset + half] = a.sub(b);
                w = w.mul(w_length);
            }
            start += length;
        }
        length *= 2;
    }
}

fn bit_reverse_permute<F: Copy>(values: &mut [F]) {
    let n = values.len();
    let bits = n.trailing_zeros();
    for i in 0..n {
        let j = (i as u32).reverse_bits() >> (32 - bits);
        let j = j as usize;
        if j > i {
            values.swap(i, j);
        }
    }
}

fn pow<F: ZkField>(base: F, mut exponent: u64) -> F {
    let mut acc = F::one();
    let mut b = base;
    while exponent > 0 {
        if exponent & 1 == 1 {
            acc = acc.mul(b);
        }
        b = b.mul(b);
        exponent >>= 1;
    }
    acc
}

/// Low-degree extension over a coset.
///
/// Given `n` evaluations of a polynomial on the size-`n` subgroup, return its
/// evaluations on a coset of the size-`n·blowup` subgroup — the redundant
/// encoding FRI's low-degree test relies on. The coset shift keeps the
/// evaluation domain disjoint from the subgroup where the trace lives, which
/// is what lets the quotient (in the full prover) be well-defined.
pub fn coset_lde<F: TwoAdicField>(evaluations: &[F], blowup: usize, shift: F) -> Vec<F> {
    let n = evaluations.len();
    assert!(n.is_power_of_two(), "LDE input must be a power of two");
    assert!(blowup.is_power_of_two() && blowup >= 1, "blowup must be a power of two");

    // 1. Interpolate: evaluations on the subgroup -> coefficients.
    let mut coefficients = evaluations.to_vec();
    intt(&mut coefficients);

    // 2. Zero-extend to the larger domain, applying the coset shift as a
    //    scaling of coefficients: evaluating p(shift · x) is evaluating the
    //    polynomial whose i-th coefficient is c_i · shift^i.
    let big = n * blowup;
    let mut extended = vec![F::zero(); big];
    let mut shift_power = F::one();
    for (i, coefficient) in coefficients.iter().enumerate() {
        extended[i] = coefficient.mul(shift_power);
        shift_power = shift_power.mul(shift);
    }

    // 3. Evaluate on the size-`big` subgroup.
    ntt(&mut extended);
    extended
}

/// Evaluate a coefficient polynomial at a single point, by Horner. Handy for
/// checking the transforms against ground truth.
pub fn evaluate<F: ZkField>(coefficients: &[F], point: F) -> F {
    let mut acc = F::zero();
    for coefficient in coefficients.iter().rev() {
        acc = acc.mul(point).add(*coefficient);
    }
    acc
}

/// Evaluate a coefficient polynomial on the coset `shift · <ω>` of size `size`.
///
/// Scaling coefficient `i` by `shift^i` turns evaluation on the subgroup (which
/// the NTT does) into evaluation at `shift · ω^j`. This is the forward half of
/// the coset machinery the STARK commits on.
pub fn coset_evaluate<F: TwoAdicField>(coefficients: &[F], shift: F, size: usize) -> Vec<F> {
    assert!(size.is_power_of_two());
    assert!(coefficients.len() <= size, "polynomial does not fit the domain");
    let mut buffer = vec![F::zero(); size];
    let mut shift_power = F::one();
    for (i, coefficient) in coefficients.iter().enumerate() {
        buffer[i] = coefficient.mul(shift_power);
        shift_power = shift_power.mul(shift);
    }
    ntt(&mut buffer);
    buffer
}

/// The inverse of [`coset_evaluate`]: evaluations on `shift · <ω>` back to
/// coefficients. Interpolate on the subgroup, then undo the `shift^i` scaling.
pub fn coset_interpolate<F: TwoAdicField>(evaluations: &[F], shift: F) -> Vec<F> {
    let mut coefficients = evaluations.to_vec();
    intt(&mut coefficients);
    let shift_inverse = shift.inverse().expect("coset shift is nonzero");
    let mut shift_power = F::one();
    for coefficient in coefficients.iter_mut() {
        *coefficient = coefficient.mul(shift_power);
        shift_power = shift_power.mul(shift_inverse);
    }
    coefficients
}