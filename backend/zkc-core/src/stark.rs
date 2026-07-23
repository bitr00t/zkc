//! The STARK prover and verifier (phase 5, Workstream I.2, with the
//! permutation argument of the wiring hardening).
//!
//! This is where phase 5 comes together and arkworks leaves the proving path.
//! Two things are proved, not one:
//!
//!   * the **gate identity** holds on every row — via the quotient
//!     `Q_gate = C_gate / Z_H`, which is a polynomial iff every gate is
//!     satisfied (I.1); and
//!   * the **wiring** holds — via a PLONK-style grand-product permutation
//!     argument over the copy constraints, so that cells tied by a copy
//!     constraint are forced to hold equal values.
//!
//! Both are folded into one composite constraint with a random challenge `α`,
//! divided by the vanishing polynomial to a single quotient `Q`, and FRI proves
//! `Q` is low-degree. Merkle openings of the trace and the grand-product column
//! `Z` tie the committed data to the quotient, and Fiat–Shamir makes it all
//! non-interactive.
//!
//! ## The permutation argument, briefly
//!
//! Each witness cell has a position and two labels: an *identity* label and a
//! *permuted* label under `σ` (built in the AIR from the copy constraints).
//! With transcript challenges `β, γ`, the prover accumulates a grand product
//!
//! ```text
//!   Z(ω^{i+1}) = Z(ω^i) · ∏_j (col_j + β·id_j + γ) / ∏_j (col_j + β·σ_j + γ)
//! ```
//!
//! starting at `Z(ω^0) = 1`. It returns to 1 after a full turn iff the two
//! multisets match, which happens iff every `σ`-cycle holds a single value —
//! i.e. iff the wiring is respected. Two constraints pin this down: `Z` starts
//! at 1 (`L_0·(Z-1) = 0`), and the recursion holds on every row
//! (`Z(ωx)·g - Z(x)·f = 0`). A broken wire makes `Z` fail to return to 1, the
//! composite is not divisible by `Z_H`, and FRI or the consistency check
//! rejects.
//!
//! ## What is and isn't covered
//!
//! Gate satisfaction and wiring are both enforced. The one hardening left
//! explicit is binding the *committed* trace and `Z` columns to low degree via
//! a FRI batch (DEEP): FRI here proves the quotient low-degree, and the trace
//! and `Z` are committed and opened for the consistency check but not
//! themselves batched into the low-degree test. That is the standard next
//! hardening and is called out plainly, in the tradition of this project
//! marking its boundaries; it does not affect the honest, forgery, or wiring
//! results below.
//!
//! Generic over the field and the [`Hasher`]; no cryptography beyond the hash.

use crate::air::{Air, Trace};
use crate::field::{TwoAdicField, ZkField};
use crate::fft::{coset_evaluate, coset_interpolate, evaluate, intt};
use crate::fri::{self, coset_shift, FriConfig, FriProof};
use crate::hash::{Digest, Hasher};
use crate::merkle::{verify_opening, MerkleTree, Opening};
use crate::plonkish::Plonkish;
use crate::transcript::Transcript;

fn domain_separator<F: ZkField>() -> Vec<F> {
    vec![F::from_u64(0x7A_6B_63_5F_73_74_61), F::from_u64(0x726b)]
}

pub struct StarkProof<F> {
    pub trace_root: Digest<F>,
    pub z_root: Digest<F>,
    pub fri: FriProof<F>,
    pub queries: Vec<StarkQuery<F>>,
    pub degree_bound: usize,
}

/// Everything opened at one FRI query's low/high positions.
pub struct StarkQuery<F> {
    pub lo: OpenedPoint<F>,
    pub hi: OpenedPoint<F>,
}

pub struct OpenedPoint<F> {
    pub a: F,
    pub b: F,
    pub c: F,
    pub trace_proof: Opening<F>,
    pub z: F,
    pub z_proof: Opening<F>,
    /// `Z` at the rotated position `p + N/n`, for the recursion constraint.
    pub z_next: F,
    pub z_next_proof: Opening<F>,
}

fn to_coeffs<F: TwoAdicField>(column: &[F]) -> Vec<F> {
    let mut coeffs = column.to_vec();
    intt(&mut coeffs);
    coeffs
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

/// Powers `ω^0 .. ω^{n-1}` of the trace-domain generator.
fn omega_powers<F: TwoAdicField>(n: usize) -> Vec<F> {
    let omega = F::two_adic_generator(n.trailing_zeros());
    let mut powers = Vec::with_capacity(n);
    let mut cur = F::one();
    for _ in 0..n {
        powers.push(cur);
        cur = cur.mul(omega);
    }
    powers
}

pub fn prove<F: TwoAdicField, H: Hasher<F>>(
    circuit: &Plonkish<F>,
    wire_values: &[F],
    config: &FriConfig,
) -> StarkProof<F> {
    let air = Air::from_plonkish(circuit);
    let trace = Air::trace(circuit, wire_values);
    prove_with_trace::<F, H>(&air, &trace, config)
}

/// The prover, taking an explicit trace. Exposed so tests can craft a trace
/// that satisfies the gates but violates the wiring — the case only the
/// permutation argument catches.
pub fn prove_with_trace<F: TwoAdicField, H: Hasher<F>>(
    air: &Air<F>,
    trace: &Trace<F>,
    config: &FriConfig,
) -> StarkProof<F> {
    let n = air.n;
    let omega_pows = omega_powers::<F>(n);
    let (id_evals, sigma_evals) = air.permutation_label_evals(&omega_pows);

    // The composite quotient's degree is dominated by the permutation
    // recursion (degree < 4n), so Q = composite/Z_H has degree < 3n.
    let degree_bound = (3 * n).next_power_of_two();
    let domain_size = degree_bound * config.blowup;
    let shift = coset_shift::<F>();
    let rotation = domain_size / n;

    // Column and selector coefficients, then coset evaluations.
    let a_c = to_coeffs(&trace.a);
    let b_c = to_coeffs(&trace.b);
    let c_c = to_coeffs(&trace.c);
    let ql_c = to_coeffs(&air.q_l);
    let qr_c = to_coeffs(&air.q_r);
    let qo_c = to_coeffs(&air.q_o);
    let qm_c = to_coeffs(&air.q_m);
    let qc_c = to_coeffs(&air.q_c);

    let a_e = coset_evaluate(&a_c, shift, domain_size);
    let b_e = coset_evaluate(&b_c, shift, domain_size);
    let c_e = coset_evaluate(&c_c, shift, domain_size);
    let ql_e = coset_evaluate(&ql_c, shift, domain_size);
    let qr_e = coset_evaluate(&qr_c, shift, domain_size);
    let qo_e = coset_evaluate(&qo_c, shift, domain_size);
    let qm_e = coset_evaluate(&qm_c, shift, domain_size);
    let qc_e = coset_evaluate(&qc_c, shift, domain_size);

    // Commit the trace, then draw the permutation challenges from it.
    let trace_leaves: Vec<Vec<F>> = (0..domain_size).map(|j| vec![a_e[j], b_e[j], c_e[j]]).collect();
    let trace_tree = MerkleTree::commit::<H>(&trace_leaves);
    let trace_root = trace_tree.root();

    let mut transcript = Transcript::<F, H>::new(&domain_separator::<F>());
    transcript.absorb_digest(&trace_root);
    let beta = transcript.challenge();
    let gamma = transcript.challenge();

    // Grand product Z on H.
    let cols_h = [&trace.a, &trace.b, &trace.c];
    let mut z_h = vec![F::zero(); n];
    z_h[0] = F::one();
    for i in 0..n - 1 {
        let mut f = F::one();
        let mut g = F::one();
        for j in 0..3 {
            f = f.mul(cols_h[j][i].add(beta.mul(id_evals[j][i])).add(gamma));
            g = g.mul(cols_h[j][i].add(beta.mul(sigma_evals[j][i])).add(gamma));
        }
        z_h[i + 1] = z_h[i].mul(f).mul(g.inverse().expect("grand-product denominator nonzero"));
    }
    let z_c = to_coeffs(&z_h);
    let z_e = coset_evaluate(&z_c, shift, domain_size);

    let z_leaves: Vec<Vec<F>> = z_e.iter().map(|v| vec![*v]).collect();
    let z_tree = MerkleTree::commit::<H>(&z_leaves);
    let z_root = z_tree.root();
    transcript.absorb_digest(&z_root);
    let alpha = transcript.challenge();
    let alpha2 = alpha.mul(alpha);

    // Label polynomials on the coset.
    let id_e: Vec<Vec<F>> = (0..3).map(|j| coset_evaluate(&to_coeffs(&id_evals[j]), shift, domain_size)).collect();
    let sigma_e: Vec<Vec<F>> = (0..3).map(|j| coset_evaluate(&to_coeffs(&sigma_evals[j]), shift, domain_size)).collect();

    // Composite constraint on the coset, then the quotient.
    let gen = F::two_adic_generator(domain_size.trailing_zeros());
    let n_field = F::from_u64(n as u64);
    let mut x = shift;
    let mut q_e = vec![F::zero(); domain_size];
    for jx in 0..domain_size {
        let cols = [a_e[jx], b_e[jx], c_e[jx]];

        // Gate constraint.
        let c_gate = air.gate_identity(cols[0], cols[1], cols[2], ql_e[jx], qr_e[jx], qo_e[jx], qm_e[jx], qc_e[jx]);

        // Permutation: f and g at this point.
        let mut f = F::one();
        let mut g = F::one();
        for j in 0..3 {
            f = f.mul(cols[j].add(beta.mul(id_e[j][jx])).add(gamma));
            g = g.mul(cols[j].add(beta.mul(sigma_e[j][jx])).add(gamma));
        }
        let z_here = z_e[jx];
        let z_shift = z_e[(jx + rotation) % domain_size];

        // L_0(x) = (x^n - 1) / (n (x - 1)); the recursion and the start.
        let xn_minus_1 = pow(x, n as u64).sub(F::one());
        let l0 = xn_minus_1.mul(n_field.mul(x.sub(F::one())).inverse().expect("x != 1 on coset"));
        let c_start = l0.mul(z_here.sub(F::one()));
        let c_rec = z_shift.mul(g).sub(z_here.mul(f));

        let composite = c_gate.add(alpha.mul(c_start)).add(alpha2.mul(c_rec));
        q_e[jx] = composite.mul(xn_minus_1.inverse().expect("Z_H nonzero on coset"));
        x = x.mul(gen);
    }
    let q_c = coset_interpolate(&q_e, shift);

    // FRI on the quotient; its query positions feed the openings.
    let fri_proof = fri::prove::<F, H>(&q_c, degree_bound, config, &mut transcript);

    let half0 = domain_size / 2;
    let open_point = |pos: usize| OpenedPoint {
        a: a_e[pos],
        b: b_e[pos],
        c: c_e[pos],
        trace_proof: trace_tree.open(pos, &trace_leaves[pos]),
        z: z_e[pos],
        z_proof: z_tree.open(pos, &z_leaves[pos]),
        z_next: z_e[(pos + rotation) % domain_size],
        z_next_proof: z_tree.open((pos + rotation) % domain_size, &z_leaves[(pos + rotation) % domain_size]),
    };
    let mut queries = Vec::with_capacity(fri_proof.queries.len());
    for query in &fri_proof.queries {
        let lo = query.index % half0;
        let hi = lo + half0;
        queries.push(StarkQuery { lo: open_point(lo), hi: open_point(hi) });
    }

    StarkProof { trace_root, z_root, fri: fri_proof, queries, degree_bound }
}

pub fn verify<F: TwoAdicField, H: Hasher<F>>(
    circuit: &Plonkish<F>,
    proof: &StarkProof<F>,
    config: &FriConfig,
) -> Result<(), String> {
    let air = Air::from_plonkish(circuit);
    verify_with_air::<F, H>(&air, proof, config)
}

pub fn verify_with_air<F: TwoAdicField, H: Hasher<F>>(
    air: &Air<F>,
    proof: &StarkProof<F>,
    config: &FriConfig,
) -> Result<(), String> {
    let n = air.n;
    let degree_bound = (3 * n).next_power_of_two();
    if proof.degree_bound != degree_bound {
        return Err("degree bound does not match the circuit".into());
    }
    let domain_size = degree_bound * config.blowup;
    let shift = coset_shift::<F>();
    let gen = F::two_adic_generator(domain_size.trailing_zeros());
    let rotation = domain_size / n;
    let n_field = F::from_u64(n as u64);

    let omega_pows = omega_powers::<F>(n);
    let (id_evals, sigma_evals) = air.permutation_label_evals(&omega_pows);
    let id_c: Vec<Vec<F>> = (0..3).map(|j| to_coeffs(&id_evals[j])).collect();
    let sigma_c: Vec<Vec<F>> = (0..3).map(|j| to_coeffs(&sigma_evals[j])).collect();

    let ql_c = to_coeffs(&air.q_l);
    let qr_c = to_coeffs(&air.q_r);
    let qo_c = to_coeffs(&air.q_o);
    let qm_c = to_coeffs(&air.q_m);
    let qc_c = to_coeffs(&air.q_c);

    // Replay: trace, permutation challenges, Z, folding challenge.
    let mut transcript = Transcript::<F, H>::new(&domain_separator::<F>());
    transcript.absorb_digest(&proof.trace_root);
    let beta = transcript.challenge();
    let gamma = transcript.challenge();
    transcript.absorb_digest(&proof.z_root);
    let alpha = transcript.challenge();
    let alpha2 = alpha.mul(alpha);

    fri::verify::<F, H>(&proof.fri, degree_bound, config, &mut transcript)?;

    if proof.queries.len() != proof.fri.queries.len() {
        return Err("stark openings do not match FRI queries".into());
    }

    let half0 = domain_size / 2;
    for (query, opened) in proof.fri.queries.iter().zip(&proof.queries) {
        let lo = query.index % half0;
        let hi = lo + half0;
        let q_lo = query.layers[0].lo;
        let q_hi = query.layers[0].hi;

        for (pos, point, q_val) in [(lo, &opened.lo, q_lo), (hi, &opened.hi, q_hi)] {
            // Trace opening.
            if !verify_opening::<F, H>(&proof.trace_root, &point.trace_proof)
                || point.trace_proof.index != pos
                || point.trace_proof.leaf != vec![point.a, point.b, point.c]
            {
                return Err(format!("bad trace opening at {pos}"));
            }
            // Z opening at pos and at the rotated position.
            let rot_pos = (pos + rotation) % domain_size;
            if !verify_opening::<F, H>(&proof.z_root, &point.z_proof)
                || point.z_proof.index != pos
                || point.z_proof.leaf != vec![point.z]
            {
                return Err(format!("bad Z opening at {pos}"));
            }
            if !verify_opening::<F, H>(&proof.z_root, &point.z_next_proof)
                || point.z_next_proof.index != rot_pos
                || point.z_next_proof.leaf != vec![point.z_next]
            {
                return Err(format!("bad rotated Z opening at {rot_pos}"));
            }

            // Rebuild the composite at z and check against Q·Z_H.
            let x = shift.mul(pow(gen, pos as u64));
            let cols = [point.a, point.b, point.c];
            let c_gate = air.gate_identity(
                cols[0], cols[1], cols[2],
                evaluate(&ql_c, x), evaluate(&qr_c, x), evaluate(&qo_c, x), evaluate(&qm_c, x), evaluate(&qc_c, x),
            );
            let mut f = F::one();
            let mut g = F::one();
            for j in 0..3 {
                f = f.mul(cols[j].add(beta.mul(evaluate(&id_c[j], x))).add(gamma));
                g = g.mul(cols[j].add(beta.mul(evaluate(&sigma_c[j], x))).add(gamma));
            }
            let xn_minus_1 = pow(x, n as u64).sub(F::one());
            let l0 = xn_minus_1.mul(n_field.mul(x.sub(F::one())).inverse().expect("x != 1 on coset"));
            let c_start = l0.mul(point.z.sub(F::one()));
            let c_rec = point.z_next.mul(g).sub(point.z.mul(f));
            let composite = c_gate.add(alpha.mul(c_start)).add(alpha2.mul(c_rec));

            if composite != q_val.mul(xn_minus_1) {
                return Err(format!("constraint check failed at {pos}: composite ≠ Q·Z_H"));
            }
        }
    }

    Ok(())
}