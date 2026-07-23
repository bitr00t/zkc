//! Tests for the Merkle commitment and Fiat–Shamir transcript
//! (phase 5, Workstreams H.1 and H.2).
//!
//! Both are written against the `Hasher` trait, so they are tested through a
//! stand-in hash defined here: a simple, transparent permutation over
//! Goldilocks. It carries NO security claim — the reviewed arithmetic hash is
//! a leaf swap the phase-5 plan makes later — but it is a real function
//! (collision-free enough on the tiny inputs here, and deterministic), which
//! is all the tree and the transcript need to be exercised. The security-
//! relevant behaviour under test is structural: openings verify, tampering is
//! caught, and challenges depend on the whole history.

use zkc_core::field::ZkField;
use zkc_core::goldilocks::Goldilocks;
use zkc_core::hash::{Digest, Hasher};
use zkc_core::merkle::{verify_opening, MerkleTree};
use zkc_core::transcript::Transcript;

/// A deliberately simple test hash: a fixed-width sponge whose round is
/// `x -> x^7 + c`, chained across inputs. Enough structure to avoid trivial
/// collisions on distinct short inputs; explicitly NOT a vetted hash.
#[derive(Clone)]
struct ToyHash;

fn g(v: u64) -> Goldilocks {
    Goldilocks::from_u64(v)
}

impl Hasher<Goldilocks> for ToyHash {
    const WIDTH: usize = 1;

    fn hash(input: &[Goldilocks]) -> Digest<Goldilocks> {
        // Absorb with a running state; x^7 is the classic low-degree S-box.
        let mut state = g(0x9E3779B97F4A7C15);
        for (i, x) in input.iter().enumerate() {
            let mixed = ZkField::add(state, ZkField::add(*x, g(i as u64 + 1)));
            state = sbox(mixed);
        }
        // One finalising round so a single-element input still diffuses.
        Digest(vec![sbox(state)])
    }

    fn compress(left: &Digest<Goldilocks>, right: &Digest<Goldilocks>) -> Digest<Goldilocks> {
        Self::hash(&[left.0[0], right.0[0]])
    }
}

fn sbox(x: Goldilocks) -> Goldilocks {
    let x2 = ZkField::mul(x, x);
    let x4 = ZkField::mul(x2, x2);
    ZkField::mul(ZkField::mul(x4, x2), x) // x^7
}

fn leaves(n: usize) -> Vec<Vec<Goldilocks>> {
    (0..n).map(|i| vec![g(i as u64 * 100 + 7), g(i as u64)]).collect()
}

// --- H.1: Merkle commitment -------------------------------------------------

#[test]
fn every_honest_opening_verifies() {
    for n in [1usize, 2, 3, 8, 16, 100] {
        let data = leaves(n);
        let tree = MerkleTree::commit::<ToyHash>(&data);
        let root = tree.root();
        for (i, leaf) in data.iter().enumerate() {
            let opening = tree.open(i, leaf);
            assert!(
                verify_opening::<_, ToyHash>(&root, &opening),
                "honest opening rejected: n={n} i={i}"
            );
        }
    }
}

#[test]
fn a_tampered_path_is_rejected() {
    // The security property: a verifier holding only the root must reject a
    // leaf that was not committed, however the proof is doctored.
    let data = leaves(16);
    let tree = MerkleTree::commit::<ToyHash>(&data);
    let root = tree.root();

    // (a) Wrong leaf value under a correct path.
    let mut forged = tree.open(5, &data[5]);
    forged.leaf[0] = g(999999);
    assert!(!verify_opening::<_, ToyHash>(&root, &forged), "a forged leaf was accepted");

    // (b) Correct leaf, corrupted sibling.
    let mut bent = tree.open(5, &data[5]);
    bent.siblings[0] = Digest(vec![g(123456)]);
    assert!(!verify_opening::<_, ToyHash>(&root, &bent), "a corrupted path was accepted");

    // (c) Correct leaf and path, but claimed at the wrong index.
    let mut moved = tree.open(5, &data[5]);
    moved.index = 6;
    assert!(!verify_opening::<_, ToyHash>(&root, &moved), "a leaf at the wrong index was accepted");
}

#[test]
fn the_root_binds_the_whole_vector() {
    // Changing any leaf changes the root — the tree commits to all of it.
    let data = leaves(8);
    let root = MerkleTree::commit::<ToyHash>(&data).root();
    let mut changed = data.clone();
    changed[3][0] = ZkField::add(changed[3][0], g(1));
    let root2 = MerkleTree::commit::<ToyHash>(&changed).root();
    assert_ne!(root, root2, "a changed leaf left the root untouched");
}

// --- H.2: Fiat–Shamir transcript --------------------------------------------

#[test]
fn replaying_the_same_transcript_gives_the_same_challenges() {
    // Prover and verifier, absorbing the same messages in the same order, must
    // agree on every challenge. This is what makes the non-interactive
    // protocol checkable at all.
    let mut prover = Transcript::<_, ToyHash>::new(&[g(1), g(2)]);
    let mut verifier = Transcript::<_, ToyHash>::new(&[g(1), g(2)]);

    prover.absorb(&[g(10), g(20)]);
    verifier.absorb(&[g(10), g(20)]);
    assert_eq!(prover.challenge(), verifier.challenge());

    prover.absorb(&[g(30)]);
    verifier.absorb(&[g(30)]);
    assert_eq!(prover.challenges(4), verifier.challenges(4));
}

#[test]
fn a_challenge_depends_on_everything_absorbed_before_it() {
    // The attack Fiat–Shamir prevents: if a challenge ignored some prior
    // message, a prover could alter that message after seeing the challenge.
    // So two transcripts differing in ANY absorbed message must diverge.
    let base = || Transcript::<_, ToyHash>::new(&[g(0)]);

    let mut a = base();
    a.absorb(&[g(1), g(2)]);
    let ca = a.challenge();

    let mut b = base();
    b.absorb(&[g(1), g(3)]); // one element different
    let cb = b.challenge();
    assert_ne!(ca, cb, "challenge ignored a change in absorbed data");

    // Order matters too.
    let mut c = base();
    c.absorb(&[g(2), g(1)]);
    assert_ne!(ca, c.challenge(), "challenge ignored absorption order");

    // And the domain separator matters.
    let mut d = Transcript::<_, ToyHash>::new(&[g(42)]);
    d.absorb(&[g(1), g(2)]);
    assert_ne!(ca, d.challenge(), "challenge ignored the domain separator");
}

#[test]
fn successive_challenges_differ_without_new_absorption() {
    // A verifier needs several independent challenges from one commitment
    // (the FRI query positions). The counter must make them distinct.
    let mut t = Transcript::<_, ToyHash>::new(&[g(7)]);
    t.absorb(&[g(1)]);
    let cs = t.challenges(8);
    for i in 0..cs.len() {
        for j in (i + 1)..cs.len() {
            assert_ne!(cs[i], cs[j], "challenges {i} and {j} collided");
        }
    }
}

#[test]
fn challenge_indices_land_in_range() {
    let mut t = Transcript::<_, ToyHash>::new(&[g(9)]);
    t.absorb(&[g(1), g(2), g(3)]);
    for _ in 0..1000 {
        let idx = t.challenge_index(64);
        assert!(idx < 64, "index {idx} out of range");
    }
}
