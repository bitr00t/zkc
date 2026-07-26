//! The Fiat–Shamir transcript (phase 5, Workstream H.2).
//!
//! A STARK is, underneath, an interactive protocol: the prover commits, the
//! verifier sends a random challenge, the prover responds, and so on. Fiat–
//! Shamir makes it non-interactive by deriving each challenge from a hash of
//! *everything committed so far* — so the prover cannot choose its challenges,
//! because it would have to fix them before committing the very data they
//! depend on.
//!
//! The transcript is that running hash. It has exactly two operations, and one
//! property worth stating precisely, because the whole soundness of the
//! non-interactive protocol rests on it:
//!
//! > A verifier that absorbs the same messages in the same order squeezes the
//! > same challenges the prover did — and changing *any* absorbed message, or
//! > its order, changes every subsequent challenge.
//!
//! If that failed — if a challenge did not depend on all prior messages — a
//! prover could commit, peek at its challenge, and go back and alter an
//! earlier commitment to suit it. That is the attack Fiat–Shamir exists to
//! prevent, and the test for it is a direct one: absorb, squeeze, then absorb
//! a different message and require the squeeze to differ.
//!
//! Generic over the [`Hasher`]; the transcript never names a concrete hash.

use crate::field::ZkField;
use crate::hash::{Digest, Hasher};

/// A running Fiat–Shamir transcript over a hasher `H`.
#[derive(Clone)]
pub struct Transcript<F, H> {
    /// Everything absorbed so far, in order. Challenges are a hash of this,
    /// which is what makes each challenge depend on the entire history.
    state: Vec<F>,
    /// Counter mixed into each squeeze, so repeated squeezes without an
    /// intervening absorb still differ (a verifier needs several independent
    /// challenges from one commitment).
    counter: u64,
    _hasher: core::marker::PhantomData<H>,
}

impl<F: ZkField, H: Hasher<F>> Transcript<F, H> {
    /// Start a transcript bound to a domain separator, so two protocols (or
    /// two phases of one) cannot be made to produce colliding challenges.
    pub fn new(domain: &[F]) -> Self {
        Transcript {
            state: domain.to_vec(),
            counter: 0,
            _hasher: core::marker::PhantomData,
        }
    }

    /// Absorb field elements — a public input, a set of evaluations. Absorbing
    /// resets the squeeze counter: challenges drawn after new data are fresh.
    pub fn absorb(&mut self, message: &[F]) {
        self.state.extend_from_slice(message);
        self.counter = 0;
    }

    /// Absorb a commitment (a Merkle root). Just its digest elements, but named
    /// separately because committing is the common case and reads better.
    pub fn absorb_digest(&mut self, digest: &Digest<F>) {
        self.absorb(digest.elements());
    }

    /// Squeeze one challenge: a hash of the whole history plus the counter.
    /// Successive squeezes differ because the counter advances.
    pub fn challenge(&mut self) -> F {
        let mut input = self.state.clone();
        input.push(F::from_u64(self.counter));
        self.counter += 1;
        let digest = H::hash(&input);
        // The first digest element is the challenge; a hash's outputs are
        // individually uniform, so one element suffices.
        digest.elements()[0]
    }

    /// A batch of independent challenges, for the several FRI query positions.
    pub fn challenges(&mut self, count: usize) -> Vec<F> {
        (0..count).map(|_| self.challenge()).collect()
    }

    /// A challenge reduced to `[0, modulus_bound)` — a query index into a
    /// domain of that size. The domain size is a power of two, so this is the
    /// low bits of the challenge's canonical representative: `challenge mod
    /// domain`. Reducing this way (rather than folding the decimal image) makes
    /// the index a genuine algebraic reduction of the challenge — the same value
    /// an in-circuit derivation would have to reproduce.
    pub fn challenge_index(&mut self, domain_size: usize) -> usize {
        assert!(domain_size.is_power_of_two(), "domain size must be a power of two");
        let challenge = self.challenge();
        challenge_mod(challenge, domain_size)
    }
}

/// Reduce a field element modulo a (power-of-two) `domain` — the low bits of its
/// canonical representative. Computed field-generically from the decimal image,
/// reducing at each digit so the accumulator stays small.
fn challenge_mod<F: ZkField>(value: F, domain: usize) -> usize {
    value
        .to_decimal()
        .bytes()
        .fold(0usize, |acc, b| (acc * 10 + (b - b'0') as usize) % domain)
}