//! Known-answer and property tests for the reviewed Poseidon-over-Goldilocks
//! hash (phase 5, hash hardening).
//!
//! The security claim rests on using the *canonical Plonky2 parameters*, so
//! the load-bearing test is the known-answer one: Plonky2's own four
//! permutation test vectors must reproduce exactly. If a single round
//! constant or an MDS entry were transcribed wrong, or the round schedule
//! were off, at least one vector would diverge. The remaining tests pin the
//! sponge and the two-to-one compression that the Merkle tree and the
//! transcript are built on, and confirm the hash drops into the commitment
//! unchanged — the "leaf swap" the roadmap promised.

use zkc_core::field::ZkField;
use zkc_core::goldilocks::Goldilocks;
use zkc_core::hash::{Digest, Hasher};
use zkc_core::merkle::{verify_opening, MerkleTree};
use zkc_core::poseidon::{permute, PoseidonGoldilocks, OUT, WIDTH};

type F = Goldilocks;
type H = PoseidonGoldilocks;

fn f(x: u64) -> F {
    F::from_u64(x)
}

// Auto-derived from Plonky2's poseidon_goldilocks `test_vectors` (neg_one = p-1 substituted).
pub const KAT: [([u64; 12], [u64; 12]); 4] = [
    ([0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
     [0x3c18a9786cb0b359, 0xc4055e3364a246c3, 0x7953db0ab48808f4, 0xc71603f33a1144ca, 0xd7709673896996dc, 0x46a84e87642f44ed, 0xd032648251ee0b3c, 0x1c687363b207df62, 0xdf8565563e8045fe, 0x40f5b37ff4254dae, 0xd070f637b431067c, 0x1792b1c4342109d7]),
    ([0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb],
     [0xd64e1e3efc5b8e9e, 0x53666633020aaa47, 0xd40285597c6a8825, 0x613a4f81e81231d2, 0x414754bfebd051f0, 0xcb1f8980294a023f, 0x6eb2a9e4d54a9d0f, 0x1902bc3af467e056, 0xf045d5eafdc6021f, 0xe4150f77caaa3be5, 0xc9bfd01d39b50cce, 0x5c0a27fcb0e1459b]),
    ([0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000],
     [0xbe0085cfc57a8357, 0xd95af71847d05c09, 0xcf55a13d33c1c953, 0x95803a74f4530e82, 0xfcd99eb30a135df1, 0xe095905e913a3029, 0xde0392461b42919b, 0x7d3260e24e81d031, 0x10d3d0465d9deaa0, 0xa87571083dfc2a47, 0xe18263681e9958f8, 0xe28e96f1ae5e60d3]),
    ([0x8ccbbbea4fe5d2b7, 0xc2af59ee9ec49970, 0x90f7e1a9e658446a, 0xdcc0630a3ab8b1b8, 0x7ff8256bca20588c, 0x5d99a7ca0c44ecfb, 0x48452b17a70fbee3, 0xeb09d654690b6c88, 0x4a55d3a39c676a88, 0xc0407a38d2285139, 0xa234bac9356386d1, 0xe1633f2bad98a52f],
     [0xa89280105650c4ec, 0xab542d53860d12ed, 0x5704148e9ccab94f, 0xd3a826d4b62da9f5, 0x8a7a6ca87892574f, 0xc7017e1cad1a674e, 0x1f06668922318e34, 0xa3b203bc8102676f, 0xfcc781b0ce382bf2, 0x934c69ff3ed14ba5, 0x504688a5996e8f13, 0x401f3f2ed524a2ba]),
];

/// The load-bearing test: the naive permutation reproduces every one of
/// Plonky2's published Goldilocks test vectors. This is what makes the
/// parameters — not this code — the thing to trust.
#[test]
fn permutation_matches_plonky2_test_vectors() {
    for (case, (input, expected)) in KAT.iter().enumerate() {
        let mut state = [F::zero(); WIDTH];
        for i in 0..WIDTH {
            state[i] = f(input[i]);
        }
        let got = permute(state);
        for i in 0..WIDTH {
            assert_eq!(
                got[i],
                f(expected[i]),
                "Poseidon test vector {case}, lane {i} diverged"
            );
        }
    }
}

/// A digest is exactly `OUT` field elements, and the trait advertises the same
/// width — what the Merkle tree and transcript assume.
#[test]
fn digest_width_is_declared_width() {
    let d = H::hash(&[f(1), f(2), f(3)]);
    assert_eq!(d.elements().len(), OUT);
    assert_eq!(<H as Hasher<F>>::WIDTH, OUT);
}

/// The sponge is a function: identical inputs give identical digests.
#[test]
fn hash_is_deterministic() {
    let a = H::hash(&[f(7), f(8), f(9)]);
    let b = H::hash(&[f(7), f(8), f(9)]);
    assert_eq!(a, b);
}

/// Distinct inputs give distinct digests on a handful of cases — including a
/// length change and a single-lane flip — so the hash is not collapsing
/// obviously-different messages.
#[test]
fn hash_separates_distinct_inputs() {
    let base = H::hash(&[f(1), f(2), f(3)]);
    assert_ne!(base, H::hash(&[f(1), f(2), f(4)]), "single-lane change");
    assert_ne!(base, H::hash(&[f(1), f(2)]), "length change");
    assert_ne!(base, H::hash(&[f(3), f(2), f(1)]), "reordering");
    // Crossing a rate boundary must still mix: 8 vs 9 elements differ.
    let eight = H::hash(&[f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8)]);
    let nine = H::hash(&[f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8), f(9)]);
    assert_ne!(eight, nine, "extra chunk must change the digest");
}

/// Compression is deterministic, order-sensitive, and sensitive to either
/// argument — the properties a Merkle internal node relies on.
#[test]
fn compress_is_order_and_input_sensitive() {
    let x = H::hash(&[f(10)]);
    let y = H::hash(&[f(20)]);
    let z = H::hash(&[f(30)]);

    assert_eq!(H::compress(&x, &y), H::compress(&x, &y), "deterministic");
    assert_ne!(H::compress(&x, &y), H::compress(&y, &x), "order matters");
    assert_ne!(H::compress(&x, &y), H::compress(&z, &y), "left matters");
    assert_ne!(H::compress(&x, &y), H::compress(&x, &z), "right matters");
}

/// The real hash drops into the Merkle commitment unchanged: honest openings
/// verify, and a tampered leaf is rejected — the same contract the stand-in
/// hash satisfied, now under reviewed parameters.
#[test]
fn merkle_commitment_works_under_poseidon() {
    let leaves: Vec<Vec<F>> = (0..6u64).map(|i| vec![f(i), f(i * 7 + 1)]).collect();
    let tree = MerkleTree::commit::<H>(&leaves);
    let root = tree.root();

    // Every honest opening verifies.
    for (i, leaf) in leaves.iter().enumerate() {
        let opening = tree.open(i, leaf);
        assert!(verify_opening::<F, H>(&root, &opening), "honest opening {i} failed");
    }

    // A forged leaf value under a valid path is rejected.
    let mut forged = tree.open(2, &leaves[2]);
    forged.leaf = vec![f(999), f(999)];
    assert!(!verify_opening::<F, H>(&root, &forged), "forged leaf accepted");

    // A corrupted sibling is rejected.
    let mut bent = tree.open(3, &leaves[3]);
    bent.siblings[0] = Digest(vec![f(1), f(2), f(3), f(4)]);
    assert!(!verify_opening::<F, H>(&root, &bent), "corrupted path accepted");
}