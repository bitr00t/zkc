//! The hash interface a STARK is built on (phase 5, Workstreams H.1/H.2).
//!
//! A FRI-based STARK's only cryptographic assumption is its hash: the Merkle
//! commitment and the Fiat–Shamir transcript both rest on it, and nothing
//! else (no pairings, no trusted setup). That makes the hash the single most
//! security-critical component, and a hand-rolled one exactly the kind of
//! thing that must not be trusted without cryptographic review.
//!
//! So the commitment and the transcript are written against this trait, never
//! against a concrete function. The phase-5 plan is to instantiate it with a
//! *reviewed* arithmetic-friendly hash (Poseidon or Rescue-Prime over
//! Goldilocks) from an audited crate; swapping that in is a leaf change,
//! because everything above only ever calls [`Hasher::hash`] and
//! [`Hasher::compress`]. Tests instantiate it with a deliberately simple
//! permutation — enough to exercise the tree and the transcript, and clearly
//! marked as not carrying any security claim of its own.
//!
//! The interface is the sponge-and-compression shape every arithmetic hash
//! offers: `hash` absorbs a variable-length slice (leaves, transcript
//! messages), `compress` combines two fixed-size digests (internal Merkle
//! nodes). Keeping both means a Merkle node never pays the cost of re-absorbing
//! through the full sponge.

use crate::field::ZkField;

/// A hash over field elements, producing fixed-width digests over the same
/// field. `WIDTH` digests compose cleanly with the field the circuit lives in,
/// which is what "arithmetic-friendly" buys.
pub trait Hasher<F: ZkField>: Clone {
    /// Digest width, in field elements.
    const WIDTH: usize;

    /// Absorb an arbitrary-length input into one digest.
    fn hash(input: &[F]) -> Digest<F>;

    /// Combine two digests into one — the internal node of a Merkle tree.
    fn compress(left: &Digest<F>, right: &Digest<F>) -> Digest<F>;
}

/// A fixed-width hash output. Small and `Clone`, so it is cheap to pass the
/// many digests a Merkle proof and a transcript move around.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Digest<F>(pub Vec<F>);

impl<F: ZkField> Digest<F> {
    pub fn elements(&self) -> &[F] {
        &self.0
    }
}