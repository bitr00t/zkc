//! The STARK prover and verifier (phase 5, Workstream I.2, with the
//! permutation argument of the wiring hardening and the DEEP/FRI batch).
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
//! Both are folded into one composite constraint with a random challenge `α`
//! and divided by the vanishing polynomial to a single quotient `Q`.
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
//! (`Z(ωx)·g - Z(x)·f = 0`).
//!
//! ## DEEP: what binds the committed columns
//!
//! Earlier versions of this file left one boundary explicit, and this note
//! records that it is closed. FRI proved the *quotient* low-degree; the trace
//! and `Z` were committed and opened, but never themselves tested. A prover
//! could therefore commit columns that are not the evaluations of any
//! low-degree polynomial, and still satisfy the pointwise identity at every
//! position — the identity is one equation per point, and a prover choosing
//! column values point by point has room to solve it. Nothing in the protocol
//! asked the columns to be polynomials at all, and the extraction argument
//! (read the witness off the trace restricted to `H`) has no content against
//! such a prover.
//!
//! The fix is the standard DEEP step, and it moves where the constraint is
//! checked. An **out-of-domain point `ζ`** is drawn from the transcript after
//! every commitment. The prover sends the columns' values there, and the
//! composite identity is checked **once, at `ζ`** — a point the prover could
//! not know while committing, and which lies outside the evaluation domain, so
//! no committed value speaks to it directly. What ties the claimed values back
//! to the commitments is a batch of quotients
//!
//! ```text
//!   (P(x) - P(ζ)) / (x - ζ)
//! ```
//!
//! one per committed column. Such a quotient is a polynomial *iff* `P` is a
//! polynomial taking the claimed value at `ζ`: a non-polynomial column has no
//! low-degree quotient, and a polynomial column with a lied-about value at `ζ`
//! leaves a pole there. The quotients are combined with random challenges into
//! one function, and FRI tests that. So a single low-degree test now carries
//! every column — trace, `Z` and quotient alike.
//!
//! Each quotient enters the batch multiplied by `λ + λ'·x^e` rather than a
//! plain `λ`, with `e` chosen so the padded term just fits under the FRI bound.
//! That is what makes the batch test each column against *its own* degree:
//! without it, a batch bounded by the quotient's degree would say nothing about
//! a trace column of a third that degree.
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

/// The six DEEP quotients: `a`, `b`, `c`, `Z` at `ζ`, `Z` at `ζω`, `Q`.
const NUM_DEEP_QUOTIENTS: usize = 6;

pub struct StarkProof<F> {
    pub trace_root: Digest<F>,
    pub z_root: Digest<F>,
    /// The quotient is committed now rather than going straight into FRI: DEEP
    /// needs a claimed value for it at `ζ`, and a claim needs a commitment to
    /// be a claim about.
    pub q_root: Digest<F>,
    pub ood: OodValues<F>,
    pub fri: FriProof<F>,
    pub queries: Vec<StarkQuery<F>>,
    pub degree_bound: usize,
}

/// Every committed column's value at the out-of-domain point `ζ`, plus `Z`'s at
/// the rotated point `ζω` that the permutation recursion needs. These six field
/// elements are where the constraint check now happens.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct OodValues<F> {
    pub a: F,
    pub b: F,
    pub c: F,
    pub z: F,
    pub z_next: F,
    pub q: F,
}

impl<F: Copy> OodValues<F> {
    fn as_slice(&self) -> [F; 6] {
        [self.a, self.b, self.c, self.z, self.z_next, self.q]
    }
}

/// Everything opened at one FRI query's low/high positions.
pub struct StarkQuery<F> {
    pub lo: OpenedPoint<F>,
    pub hi: OpenedPoint<F>,
}

/// One position's openings. The rotated `Z` opening earlier versions carried is
/// gone: the rotation is handled at `ζ` now, so the in-domain openings only
/// have to rebuild the DEEP batch.
pub struct OpenedPoint<F> {
    pub a: F,
    pub b: F,
    pub c: F,
    pub trace_proof: Opening<F>,
    pub z: F,
    pub z_proof: Opening<F>,
    pub q: F,
    pub q_proof: Opening<F>,
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

/// Draw `ζ` from the transcript, rejecting the points at which DEEP would be
/// undefined or meaningless.
///
/// Three rejections. **Inside the evaluation coset**, `x - ζ` vanishes at a
/// domain point, so the quotient is undefined — and worse, `ζ` would be a point
/// the commitments already speak to, which defeats the purpose of going out of
/// domain. **On the trace domain `H`**, the vanishing polynomial `Z_H(ζ)` is
/// zero and the check `composite(ζ) = Q(ζ)·Z_H(ζ)` degenerates to `0 = 0`.
/// **At `ζ = 1`**, `L_0` is `0/0`.
///
/// Both sides run this, so both must run it identically — hence one function
/// rather than two implementations that agree today. A rejection is
/// astronomically unlikely (the excluded set has `|domain| + n + 1` elements),
/// but a protocol that is sound only because a bad draw is improbable is a
/// protocol with a hole in it, so the loop is real and its exhaustion is an
/// error rather than an assumption.
fn draw_ood_point<F: TwoAdicField, H: Hasher<F>>(
    transcript: &mut Transcript<F, H>,
    n: usize,
    domain_size: usize,
    shift: F,
) -> Option<F> {
    let coset_signature = pow(shift, domain_size as u64);
    for _ in 0..64 {
        let candidate = transcript.challenge();
        let in_coset = pow(candidate, domain_size as u64) == coset_signature;
        let on_trace_domain = pow(candidate, n as u64) == F::one();
        if !in_coset && !on_trace_domain && candidate != F::one() {
            return Some(candidate);
        }
    }
    None
}

/// The DEEP batch at one point of the evaluation domain.
///
/// Prover and verifier both need this — the prover across the whole domain to
/// build the FRI input, the verifier at the queried positions to check what FRI
/// opened. Writing it once is the point: two agreeing implementations of a
/// random linear combination is exactly the duplication that rots into a
/// soundness bug nobody can see, because both sides stay self-consistent while
/// drifting away from the protocol.
///
/// `adjust_column` and `adjust_quotient` are the degree corrections described in
/// the module docs, already raised to the right power of `x`.
#[allow(clippy::too_many_arguments)]
fn deep_batch<F: ZkField>(
    lambdas: &[F],
    ood: &OodValues<F>,
    a: F,
    b: F,
    c: F,
    z: F,
    q: F,
    inv_zeta: F,
    inv_zeta_next: F,
    adjust_column: F,
    adjust_quotient: F,
) -> F {
    let quotients = [
        (a.sub(ood.a).mul(inv_zeta), adjust_column),
        (b.sub(ood.b).mul(inv_zeta), adjust_column),
        (c.sub(ood.c).mul(inv_zeta), adjust_column),
        (z.sub(ood.z).mul(inv_zeta), adjust_column),
        (z.sub(ood.z_next).mul(inv_zeta_next), adjust_column),
        (q.sub(ood.q).mul(inv_zeta), adjust_quotient),
    ];
    let mut acc = F::zero();
    for (i, (quotient, adjust)) in quotients.iter().enumerate() {
        let coefficient = lambdas[2 * i].add(lambdas[2 * i + 1].mul(*adjust));
        acc = acc.add(coefficient.mul(*quotient));
    }
    acc
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
/// permutation argument catches — or one that is no polynomial at all, the case
/// only DEEP catches.
pub fn prove_with_trace<F: TwoAdicField, H: Hasher<F>>(
    air: &Air<F>,
    trace: &Trace<F>,
    config: &FriConfig,
) -> StarkProof<F> {
    prove_inner::<F, H>(air, trace, config, None)
}

/// A prover that commits a column which is *not* the low-degree extension of
/// the trace: the `a` column's committed evaluation at `position` is shifted by
/// `delta`, while the quotient is built from the honest one.
///
/// This is the shape of the prover DEEP exists to refuse, and it is worth
/// stating why it is not simply "a prover that lies". Everything here stays
/// self-consistent. The quotient really is low-degree, because it was computed
/// from the honest polynomial. The constraint identity really does hold — at
/// every position except one. The Merkle openings really do check out, because
/// the corrupted value is what was committed. Before the DEEP batch, the only
/// thing that could catch this was the identity check at the queried positions,
/// so the corruption was invisible unless a query happened to land on it — and
/// a prover can retry until none does, since the positions are a public
/// function of the commitment.
///
/// Exposed for the same reason as [`prove_with_trace`]: the tests that matter
/// are the ones an honest prover cannot express.
pub fn prove_with_corrupted_column<F: TwoAdicField, H: Hasher<F>>(
    air: &Air<F>,
    trace: &Trace<F>,
    config: &FriConfig,
    position: usize,
    delta: F,
) -> StarkProof<F> {
    prove_inner::<F, H>(air, trace, config, Some((position, delta)))
}

fn prove_inner<F: TwoAdicField, H: Hasher<F>>(
    air: &Air<F>,
    trace: &Trace<F>,
    config: &FriConfig,
    corruption: Option<(usize, F)>,
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

    // What gets committed need not be what the quotient is built from — that
    // gap is exactly what `prove_with_corrupted_column` exercises, and what the
    // DEEP batch closes. For an honest prover the two are the same vector.
    let a_committed = match corruption {
        None => a_e.clone(),
        Some((position, delta)) => {
            let mut corrupted = a_e.clone();
            corrupted[position] = corrupted[position].add(delta);
            corrupted
        }
    };

    // Commit the trace, then draw the permutation challenges from it.
    let trace_leaves: Vec<Vec<F>> =
        (0..domain_size).map(|j| vec![a_committed[j], b_e[j], c_e[j]]).collect();
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

    // Commit the quotient, then go out of domain. Every column the verifier
    // will hear a claim about is now fixed, so ζ cannot be chosen to suit them.
    let q_leaves: Vec<Vec<F>> = q_e.iter().map(|v| vec![*v]).collect();
    let q_tree = MerkleTree::commit::<H>(&q_leaves);
    let q_root = q_tree.root();
    transcript.absorb_digest(&q_root);

    let zeta = draw_ood_point::<F, H>(&mut transcript, n, domain_size, shift)
        .expect("an acceptable out-of-domain point");
    let omega = F::two_adic_generator(n.trailing_zeros());
    let zeta_next = zeta.mul(omega);

    let ood = OodValues {
        a: evaluate(&a_c, zeta),
        b: evaluate(&b_c, zeta),
        c: evaluate(&c_c, zeta),
        z: evaluate(&z_c, zeta),
        z_next: evaluate(&z_c, zeta_next),
        q: evaluate(&q_c, zeta),
    };
    transcript.absorb(&ood.as_slice());
    let lambdas = transcript.challenges(2 * NUM_DEEP_QUOTIENTS);

    // The DEEP batch across the domain, then FRI on it. Degree corrections: the
    // column quotients have degree < n-1 and the quotient's < degree_bound-1, so
    // each padded term lands just inside the FRI bound.
    let column_exponent = (degree_bound - (n - 1)) as u64;
    let mut batch_e = vec![F::zero(); domain_size];
    let mut x = shift;
    for jx in 0..domain_size {
        let inv_zeta = x.sub(zeta).inverse().expect("ζ is outside the evaluation domain");
        let inv_zeta_next = x.sub(zeta_next).inverse().expect("ζω is outside the evaluation domain");
        batch_e[jx] = deep_batch(
            &lambdas, &ood, a_committed[jx], b_e[jx], c_e[jx], z_e[jx], q_e[jx],
            inv_zeta, inv_zeta_next, pow(x, column_exponent), x,
        );
        x = x.mul(gen);
    }
    let batch_c = coset_interpolate(&batch_e, shift);
    let fri_proof = fri::prove::<F, H>(&batch_c, degree_bound, config, &mut transcript);

    let half0 = domain_size / 2;
    let open_point = |pos: usize| OpenedPoint {
        a: a_committed[pos],
        b: b_e[pos],
        c: c_e[pos],
        trace_proof: trace_tree.open(pos, &trace_leaves[pos]),
        z: z_e[pos],
        z_proof: z_tree.open(pos, &z_leaves[pos]),
        q: q_e[pos],
        q_proof: q_tree.open(pos, &q_leaves[pos]),
    };
    let mut queries = Vec::with_capacity(fri_proof.queries.len());
    for query in &fri_proof.queries {
        let lo = query.index % half0;
        let hi = lo + half0;
        queries.push(StarkQuery { lo: open_point(lo), hi: open_point(hi) });
    }

    StarkProof { trace_root, z_root, q_root, ood, fri: fri_proof, queries, degree_bound }
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

    // Replay: trace, permutation challenges, Z, folding challenge, quotient.
    let mut transcript = Transcript::<F, H>::new(&domain_separator::<F>());
    transcript.absorb_digest(&proof.trace_root);
    let beta = transcript.challenge();
    let gamma = transcript.challenge();
    transcript.absorb_digest(&proof.z_root);
    let alpha = transcript.challenge();
    let alpha2 = alpha.mul(alpha);
    transcript.absorb_digest(&proof.q_root);

    let zeta = draw_ood_point::<F, H>(&mut transcript, n, domain_size, shift)
        .ok_or("no acceptable out-of-domain point")?;
    let omega = F::two_adic_generator(n.trailing_zeros());
    let zeta_next = zeta.mul(omega);
    let ood = &proof.ood;
    transcript.absorb(&ood.as_slice());
    let lambdas = transcript.challenges(2 * NUM_DEEP_QUOTIENTS);

    // --- The constraint check, once, out of domain ---
    //
    // This is the whole of the arithmetic check now. On its own it says
    // nothing: the six values could be invented, and inventing six values that
    // satisfy one equation is easy. What makes it binding is the DEEP batch
    // below, which is low-degree only if each of them is the true value of the
    // committed column at ζ.
    let c_gate = air.gate_identity(
        ood.a, ood.b, ood.c,
        evaluate(&ql_c, zeta), evaluate(&qr_c, zeta), evaluate(&qo_c, zeta),
        evaluate(&qm_c, zeta), evaluate(&qc_c, zeta),
    );
    let cols = [ood.a, ood.b, ood.c];
    let mut f = F::one();
    let mut g = F::one();
    for j in 0..3 {
        f = f.mul(cols[j].add(beta.mul(evaluate(&id_c[j], zeta))).add(gamma));
        g = g.mul(cols[j].add(beta.mul(evaluate(&sigma_c[j], zeta))).add(gamma));
    }
    let z_h_zeta = pow(zeta, n as u64).sub(F::one());
    let l0 = z_h_zeta.mul(
        n_field.mul(zeta.sub(F::one())).inverse().ok_or("ζ = 1 is excluded by the draw")?,
    );
    let c_start = l0.mul(ood.z.sub(F::one()));
    let c_rec = ood.z_next.mul(g).sub(ood.z.mul(f));
    let composite = c_gate.add(alpha.mul(c_start)).add(alpha2.mul(c_rec));
    if composite != ood.q.mul(z_h_zeta) {
        return Err("constraint check failed at ζ: composite ≠ Q·Z_H".into());
    }

    // --- The low-degree test, now carrying every committed column ---
    fri::verify::<F, H>(&proof.fri, degree_bound, config, &mut transcript)?;

    if proof.queries.len() != proof.fri.queries.len() {
        return Err("stark openings do not match FRI queries".into());
    }

    let column_exponent = (degree_bound - (n - 1)) as u64;
    let half0 = domain_size / 2;
    for (query, opened) in proof.fri.queries.iter().zip(&proof.queries) {
        let lo = query.index % half0;
        let hi = lo + half0;

        for (pos, point, batch_value) in
            [(lo, &opened.lo, query.layers[0].lo), (hi, &opened.hi, query.layers[0].hi)]
        {
            if !verify_opening::<F, H>(&proof.trace_root, &point.trace_proof)
                || point.trace_proof.index != pos
                || point.trace_proof.leaf != vec![point.a, point.b, point.c]
            {
                return Err(format!("bad trace opening at {pos}"));
            }
            if !verify_opening::<F, H>(&proof.z_root, &point.z_proof)
                || point.z_proof.index != pos
                || point.z_proof.leaf != vec![point.z]
            {
                return Err(format!("bad Z opening at {pos}"));
            }
            if !verify_opening::<F, H>(&proof.q_root, &point.q_proof)
                || point.q_proof.index != pos
                || point.q_proof.leaf != vec![point.q]
            {
                return Err(format!("bad quotient opening at {pos}"));
            }

            // Rebuild the batch from the opened columns and compare against the
            // value FRI proved low-degree. Agreement here is what carries the
            // low-degree property back to each individual column.
            let x = shift.mul(pow(gen, pos as u64));
            let inv_zeta = x.sub(zeta).inverse().ok_or("ζ landed in the evaluation domain")?;
            let inv_zeta_next =
                x.sub(zeta_next).inverse().ok_or("ζω landed in the evaluation domain")?;
            let expected = deep_batch(
                &lambdas, ood, point.a, point.b, point.c, point.z, point.q,
                inv_zeta, inv_zeta_next, pow(x, column_exponent), x,
            );
            if expected != batch_value {
                return Err(format!("DEEP batch mismatch at {pos}"));
            }
        }
    }

    Ok(())
}
