//! FRI: the low-degree test at the heart of the STARK (phase 5, I.2).
//!
//! Everything else in phase 5 exists to reduce a statement to one FRI can
//! answer: *is this committed function the evaluation of a low-degree
//! polynomial?* The STARK builds a quotient that is a polynomial iff the
//! circuit is satisfied, and FRI is what proves the quotient's degree — so FRI
//! is the step that turns "I checked it" into "I can prove I checked it"
//! succinctly, with nothing but a hash.
//!
//! ## The fold
//!
//! FRI shrinks the problem by half each round. Split a polynomial into even and
//! odd parts, `f(x) = f_e(x²) + x·f_o(x²)`, and combine them with a verifier
//! challenge `α`: `f'(x²) = f_e(x²) + α·f_o(x²)`. The new polynomial has half
//! the degree and lives on a domain of half the size (the squares). In point
//! form, using `f(x)` and `f(-x)` (which the domain provides as a sibling pair,
//! since `-x = x·ω^{m/2}`):
//!
//! ```text
//!   f'(x²) = (f(x) + f(-x))/2  +  α · (f(x) - f(-x)) / (2x)
//! ```
//!
//! After `log₂(degree bound)` rounds the polynomial is a constant, sent in the
//! clear. Soundness comes from the query phase: a prover who folded a
//! *high*-degree function cannot keep the fold relation consistent across
//! rounds at random points, so each query catches a cheat with constant
//! probability, and many queries drive the error down.

use crate::field::{TwoAdicField, ZkField};
use crate::fft::coset_evaluate;
use crate::hash::{Digest, Hasher};
use crate::merkle::{verify_opening, MerkleTree, Opening};
use crate::transcript::Transcript;

/// A fixed coset shift for the FRI evaluation domain, disjoint from the
/// subgroups the trace lives on.
pub fn coset_shift<F: ZkField>() -> F {
    F::from_u64(7)
}

#[derive(Clone)]
pub struct FriConfig {
    /// Domain-size to degree-bound ratio; larger means more redundancy and
    /// fewer queries for the same soundness.
    pub blowup: usize,
    /// Independent query positions. Soundness error falls exponentially in this.
    pub num_queries: usize,
}

impl Default for FriConfig {
    fn default() -> Self {
        FriConfig { blowup: 4, num_queries: 32 }
    }
}

/// One query's opened pair at one fold layer, with Merkle proofs.
pub struct LayerOpening<F> {
    pub lo: F,
    pub hi: F,
    pub lo_proof: Opening<F>,
    pub hi_proof: Opening<F>,
}

pub struct FriQuery<F> {
    pub index: usize,
    pub layers: Vec<LayerOpening<F>>,
}

pub struct FriProof<F> {
    pub roots: Vec<Digest<F>>,
    pub final_poly: Vec<F>,
    pub queries: Vec<FriQuery<F>>,
    /// Domain-0 size, so the verifier can rebuild every layer's geometry.
    pub domain_size: usize,
}

/// Fold one layer's evaluations to the next, given challenge `α`. The domain of
/// `layer` is `shift · <gen>` of size `m`; the result lives on `shift² · <gen²>`
/// of size `m/2`.
fn fold_layer<F: TwoAdicField>(layer: &[F], shift: F, alpha: F) -> Vec<F> {
    let m = layer.len();
    let half = m / 2;
    let gen = F::two_adic_generator(m.trailing_zeros());
    let two_inverse = F::from_u64(2).inverse().expect("2 is invertible");
    let mut folded = vec![F::zero(); half];
    let mut x = shift; // x = shift · gen^j
    for j in 0..half {
        let f_lo = layer[j];
        let f_hi = layer[j + half];
        let sum = f_lo.add(f_hi).mul(two_inverse);
        let diff = f_lo.sub(f_hi).mul(two_inverse).mul(x.inverse().expect("domain point nonzero"));
        folded[j] = sum.add(alpha.mul(diff));
        x = x.mul(gen);
    }
    folded
}

/// Commit a layer's evaluations as a Merkle tree, one evaluation per leaf.
fn commit_layer<F: ZkField, H: Hasher<F>>(layer: &[F]) -> MerkleTree<F> {
    let leaves: Vec<Vec<F>> = layer.iter().map(|v| vec![*v]).collect();
    MerkleTree::commit::<H>(&leaves)
}

/// Prove that `coefficients` (degree `< degree_bound`) is low-degree.
///
/// Returns the FRI proof. The transcript is threaded through so the STARK can
/// bind FRI's challenges to its trace commitment — the folding challenges and
/// the query positions both come from it.
pub fn prove<F: TwoAdicField, H: Hasher<F>>(
    coefficients: &[F],
    degree_bound: usize,
    config: &FriConfig,
    transcript: &mut Transcript<F, H>,
) -> FriProof<F> {
    assert!(degree_bound.is_power_of_two());
    let domain_size = degree_bound * config.blowup;
    let shift = coset_shift::<F>();

    // Layer 0: the polynomial on the full coset.
    let mut layer = coset_evaluate(coefficients, shift, domain_size);
    let mut layer_shift = shift;

    let num_rounds = degree_bound.trailing_zeros() as usize; // fold to size = blowup
    let mut trees = Vec::with_capacity(num_rounds);
    let mut roots = Vec::with_capacity(num_rounds);
    let mut alphas = Vec::with_capacity(num_rounds);
    let mut layers = Vec::with_capacity(num_rounds);

    for _ in 0..num_rounds {
        let tree = commit_layer::<F, H>(&layer);
        let root = tree.root();
        transcript.absorb_digest(&root);
        let alpha = transcript.challenge();

        layers.push(layer.clone());
        trees.push(tree);
        roots.push(root);
        alphas.push(alpha);

        layer = fold_layer(&layer, layer_shift, alpha);
        layer_shift = layer_shift.mul(layer_shift);
    }

    // `layer` is now the final, lowest-degree codeword (size `blowup`); it is a
    // constant polynomial's evaluations if the input was genuinely low-degree.
    let final_poly = layer.clone();
    for element in &final_poly {
        transcript.absorb(&[*element]);
    }

    // Query phase: positions from the transcript, openings at each layer.
    let half0 = domain_size / 2;
    let mut queries = Vec::with_capacity(config.num_queries);
    for _ in 0..config.num_queries {
        let index = transcript.challenge_index(half0);
        let mut layer_openings = Vec::with_capacity(num_rounds);
        let mut position = index;
        let mut size = domain_size;
        for round in 0..num_rounds {
            let half = size / 2;
            let lo = position % half;
            let hi = lo + half;
            let tree = &trees[round];
            let evals = &layers[round];
            layer_openings.push(LayerOpening {
                lo: evals[lo],
                hi: evals[hi],
                lo_proof: tree.open(lo, &[evals[lo]]),
                hi_proof: tree.open(hi, &[evals[hi]]),
            });
            position = lo;
            size = half;
        }
        queries.push(FriQuery { index, layers: layer_openings });
    }

    FriProof { roots, final_poly, queries, domain_size }
}

/// Verify a FRI proof: replay the transcript for challenges, then check every
/// query's fold chain and Merkle openings, and that the final codeword is a
/// constant.
pub fn verify<F: TwoAdicField, H: Hasher<F>>(
    proof: &FriProof<F>,
    degree_bound: usize,
    config: &FriConfig,
    transcript: &mut Transcript<F, H>,
) -> Result<(), String> {
    let domain_size = proof.domain_size;
    if domain_size != degree_bound * config.blowup {
        return Err("domain size does not match degree bound".into());
    }
    let num_rounds = degree_bound.trailing_zeros() as usize;
    if proof.roots.len() != num_rounds {
        return Err("wrong number of fold layers".into());
    }
    // The query count is the verifier's security parameter: a proof with fewer
    // queries than the config demands is weaker, so it must be rejected rather
    // than silently accepted for the queries it does contain.
    if proof.queries.len() != config.num_queries {
        return Err("proof does not contain the required number of queries".into());
    }
    let shift = coset_shift::<F>();

    // Replay to recover the folding challenges, in lockstep with the prover.
    let mut alphas = Vec::with_capacity(num_rounds);
    for root in &proof.roots {
        transcript.absorb_digest(root);
        alphas.push(transcript.challenge());
    }
    for element in &proof.final_poly {
        transcript.absorb(&[*element]);
    }

    // The final codeword must be a constant (degree 0): all entries equal.
    let final_constant = proof.final_poly[0];
    if proof.final_poly.iter().any(|v| *v != final_constant) {
        return Err("final FRI codeword is not constant (input was not low-degree)".into());
    }

    let half0 = domain_size / 2;
    for query in &proof.queries {
        // Positions are the verifier's to derive, not the prover's to choose.
        let index = transcript.challenge_index(half0);
        if index != query.index {
            return Err("query index was not drawn from the transcript".into());
        }

        let mut position = index;
        let mut size = domain_size;
        let mut layer_shift = shift;
        let mut previous_fold: Option<F> = None;

        for (round, opening) in query.layers.iter().enumerate() {
            let half = size / 2;
            let lo = position % half;
            let hi = lo + half;

            // Merkle: both openings must sit under this layer's committed root.
            if !verify_opening::<F, H>(&proof.roots[round], &opening.lo_proof)
                || opening.lo_proof.index != lo
                || opening.lo_proof.leaf != vec![opening.lo]
            {
                return Err(format!("bad low opening at round {round}"));
            }
            if !verify_opening::<F, H>(&proof.roots[round], &opening.hi_proof)
                || opening.hi_proof.index != hi
                || opening.hi_proof.leaf != vec![opening.hi]
            {
                return Err(format!("bad high opening at round {round}"));
            }

            // Chain: the previous round's fold must equal whichever of this
            // layer's two openings sits at the carried-in position.
            if let Some(expected) = previous_fold {
                let actual = if position < half { opening.lo } else { opening.hi };
                if actual != expected {
                    return Err(format!("fold inconsistency entering round {round}"));
                }
            }

            // This round's fold, to check against the next layer.
            let gen = F::two_adic_generator(size.trailing_zeros());
            let x = layer_shift.mul(pow(gen, lo as u64));
            let two_inverse = F::from_u64(2).inverse().unwrap();
            let sum = opening.lo.add(opening.hi).mul(two_inverse);
            let diff = opening
                .lo
                .sub(opening.hi)
                .mul(two_inverse)
                .mul(x.inverse().unwrap());
            previous_fold = Some(sum.add(alphas[round].mul(diff)));

            position = lo;
            size = half;
            layer_shift = layer_shift.mul(layer_shift);
        }

        // The last fold must match the final codeword at the carried position.
        let expected_final = previous_fold.expect("at least one round");
        if proof.final_poly[position % proof.final_poly.len()] != expected_final {
            return Err("final fold does not match the committed constant".into());
        }
    }

    Ok(())
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