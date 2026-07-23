//! Merkle commitment over the column evaluations FRI queries (phase 5, H.1).
//!
//! A STARK commits to each column of its trace by Merkle-hashing the column's
//! evaluations; FRI then opens a handful of leaves and the verifier checks each
//! against the committed root. The security argument is entirely about the
//! *opening*: a root binds the prover to a fixed vector of leaves, and an
//! authentication path is what convinces a verifier that a claimed leaf really
//! sits at a claimed position under that root. So the code that matters is
//! [`verify_opening`], and the tests that matter are the ones that tamper with
//! a path and require it to be rejected.
//!
//! Generic over both the field and the [`Hasher`]: the tree never names a
//! concrete hash, so the reviewed one drops in unchanged.

use crate::field::ZkField;
use crate::hash::{Digest, Hasher};

/// A commitment to a vector of leaves: the root, plus the tree kept for
/// producing openings. Leaves are padded to a power of two with the zero
/// element, so a path length is exactly `log2(n)` and every position is valid.
pub struct MerkleTree<F> {
    /// `layers[0]` is the leaves; `layers.last()` is a single-element root.
    layers: Vec<Vec<Digest<F>>>,
}

/// An authentication path: the sibling digest at each level from leaf to root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opening<F> {
    pub index: usize,
    pub leaf: Vec<F>,
    pub siblings: Vec<Digest<F>>,
}

impl<F: ZkField> MerkleTree<F> {
    /// Commit to one leaf per row. Each leaf is itself a slice of field
    /// elements (a row across committed columns), hashed to a digest.
    pub fn commit<H: Hasher<F>>(leaves: &[Vec<F>]) -> Self {
        assert!(!leaves.is_empty(), "cannot commit to an empty set of leaves");

        // Pad to a power of two so the tree is perfect and paths are uniform.
        let padded = leaves.len().next_power_of_two();
        let mut level: Vec<Digest<F>> = leaves.iter().map(|leaf| H::hash(leaf)).collect();
        let zero_leaf = H::hash(&[F::zero()]);
        level.resize(padded, zero_leaf);

        let mut layers = vec![level];
        while layers.last().unwrap().len() > 1 {
            let current = layers.last().unwrap();
            let next: Vec<Digest<F>> = current
                .chunks(2)
                .map(|pair| H::compress(&pair[0], &pair[1]))
                .collect();
            layers.push(next);
        }
        MerkleTree { layers }
    }

    pub fn root(&self) -> Digest<F> {
        self.layers.last().unwrap()[0].clone()
    }

    /// Produce the opening for a leaf: its value and the sibling at each level.
    pub fn open(&self, index: usize, leaf: &[F]) -> Opening<F> {
        assert!(index < self.layers[0].len(), "leaf index out of range");
        let mut siblings = Vec::new();
        let mut position = index;
        for level in &self.layers[..self.layers.len() - 1] {
            // Sibling is the other child of this node's parent.
            let sibling = position ^ 1;
            siblings.push(level[sibling].clone());
            position >>= 1;
        }
        Opening { index, leaf: leaf.to_vec(), siblings }
    }
}

/// Recompute the root from an opening and compare. This is the whole security
/// check: a verifier that holds only the root can confirm a leaf without ever
/// seeing the tree.
pub fn verify_opening<F: ZkField, H: Hasher<F>>(root: &Digest<F>, opening: &Opening<F>) -> bool {
    let mut running = H::hash(&opening.leaf);
    let mut position = opening.index;
    for sibling in &opening.siblings {
        // At each level, our node is the left child on an even index, the
        // right child on an odd one; compose accordingly.
        running = if position & 1 == 0 {
            H::compress(&running, sibling)
        } else {
            H::compress(sibling, &running)
        };
        position >>= 1;
    }
    &running == root
}