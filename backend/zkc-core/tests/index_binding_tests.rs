//! Phase 7, O — the query index: the boundary of what determinacy proves, and
//! the sound derivation that crosses it.
//!
//! In-circuit Fiat-Shamir derived the fold challenge (see fri_verifier_tests).
//! The query index is the other Fiat-Shamir value, and it is derived here as
//! an honest algebraic reduction — `challenge mod domain`, the low bits of the
//! canonical representative.
//!
//! This file tells the story in two halves, and the second half now exists.
//!
//! The first half is the finding. The *natural* in-circuit binding,
//! `challenge == index + domain*high`, is proved determinate by the frontend
//! and is nevertheless forgeable: `high` is free. Determinacy rules out
//! under-constrained outputs; it does not certify that an output is a canonical
//! reduction, because that is a range property.
//!
//! The second half closes it. With the `bits` hint the range is expressible:
//! the index is no longer *related* to the challenge but *read off* a pinned
//! 64-bit decomposition of it, and the non-canonical decompositions Goldilocks
//! admits — the field wraps below 2^64 — are ruled out by an explicit
//! canonicity check. The forgery that satisfies the naive binding does not
//! satisfy this one, and the test below says so by enumeration rather than by
//! assertion: it walks *every* 64-bit string congruent to the challenge, and
//! finds exactly one index survives.

use std::collections::HashMap;

use zkc_core::field::ZkField;
use zkc_core::goldilocks::Goldilocks;
use zkc_core::hash::{Digest, Hasher};
use zkc_core::ir::{Ir, Unmet};
use zkc_core::transcript::Transcript;
use zkc_core::witness::{solve, SolveInputs};

type F = Goldilocks;
fn g(v: u64) -> F {
    F::from_u64(v)
}
fn sbox(x: F) -> F {
    let x2 = x.mul(x);
    x2.mul(x2).mul(x2).mul(x)
}
#[derive(Clone)]
struct H;
impl Hasher<F> for H {
    const WIDTH: usize = 1;
    fn hash(input: &[F]) -> Digest<F> {
        let mut acc = F::zero();
        for (i, x) in input.iter().enumerate() {
            acc = acc.add(x.add(g(i as u64 + 1)));
        }
        Digest(vec![sbox(acc)])
    }
    fn compress(l: &Digest<F>, r: &Digest<F>) -> Digest<F> {
        Digest(vec![sbox(l.0[0].add(g(2))).add(sbox(r.0[0].add(g(3))))])
    }
}

/// The canonical reduction the in-circuit derivation would target.
fn value_mod(value: F, domain: usize) -> usize {
    value
        .to_decimal()
        .bytes()
        .fold(0usize, |acc, b| (acc * 10 + (b - b'0') as usize) % domain)
}

#[test]
fn the_query_index_is_an_algebraic_reduction_of_the_challenge() {
    // Two identical transcripts: one draws the index, the other the raw
    // challenge. The index must be exactly .
    let domain = 64usize;
    let mut t_index = Transcript::<_, H>::new(&[g(9)]);
    t_index.absorb(&[g(1), g(2), g(3)]);
    let mut t_raw = Transcript::<_, H>::new(&[g(9)]);
    t_raw.absorb(&[g(1), g(2), g(3)]);

    for _ in 0..64 {
        let idx = t_index.challenge_index(domain);
        let raw = t_raw.challenge();
        assert!(idx < domain);
        assert_eq!(idx, value_mod(raw, domain), "the index is challenge mod domain");
    }
}

// The naive in-circuit binding, compiled from examples/index_from_challenge.zkc.
const INDEX_BINDING_IR: &str = include_str!("fixtures/index_from_challenge.ir.json");

#[test]
fn naive_index_binding_is_determinate_but_unsound() {
    // The frontend PROVES this circuit determinate —  is a function of its
    // inputs. Yet every index in {0,1,2,3} satisfies it: the prover picks
    // high = (challenge - index)/4 to hit any index it likes. Determinacy rules
    // out under-constrained *outputs*; it does not, and cannot, certify that an
    // output equals a canonical reduction. That is a range property, and needs a
    // bounded decomposition the language cannot yet express.
    let ir = Ir::from_json(INDEX_BINDING_IR).unwrap();
    let challenge = g(0x0123_4567_89ab_cdef);
    let inv4 = g(4).inverse().unwrap();

    let mut satisfying = Vec::new();
    for index in 0u64..4 {
        let idx_f = g(index);
        let high = challenge.sub(idx_f).mul(inv4); // always solvable — the hole
        let inputs: HashMap<String, F> = [
            ("challenge", challenge),
            ("b0", g(index & 1)),
            ("b1", g((index >> 1) & 1)),
            ("high", high),
            ("idx", idx_f),
        ]
        .iter()
        .map(|(k, v)| ((*k).to_string(), *v))
        .collect();
        let wires = solve::<F>(
            &ir,
            &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
        )
        .unwrap();
        if ir.is_satisfied::<F>(&wires) {
            satisfying.push(index);
        }
    }

    assert_eq!(
        satisfying,
        vec![0, 1, 2, 3],
        "every index satisfies the naive binding — it is determinate but unsound"
    );
}

// ---------------------------------------------------------------------------
// The sound derivation (std/query_index4.zkc) — the loop closed.
// ---------------------------------------------------------------------------

const SOUND_IR: &str = include_str!("fixtures/index_from_challenge_sound.ir.json");

/// Goldilocks: p = 2^64 - 2^32 + 1. Below 2^64, which is the whole subtlety.
const P: u128 = 18_446_744_069_414_584_321;
const TWO_64: u128 = 1u128 << 64;
const DOMAIN: u128 = 4;

/// Every 64-bit string that reconstructs to `c` in the field — the prover's
/// complete freedom under the pinned decomposition, so a test that walks this
/// list has considered every possible witness rather than a few guesses.
///
/// There are at most two. `c` itself always works; `c + p` also fits in 64 bits
/// exactly when `c < 2^64 - p = 2^32 - 1`, and that second string is the reason
/// the gadget carries a canonicity check at all. Its low bits differ from `c`'s,
/// so without the check it would hand the prover a second, freely chosen index.
fn decompositions(c: u128) -> Vec<u128> {
    let mut all = vec![c];
    if c + P < TWO_64 {
        all.push(c + P);
    }
    all
}

/// Run the sound circuit with a prover that supplies `value`'s bits as advice
/// and claims `idx`. Returns the obligations the result fails to meet — empty
/// means the circuit accepted.
fn attempt(ir: &Ir, challenge: u128, value: u128, idx: u128) -> Vec<Unmet> {
    let overrides: HashMap<String, F> = (0..64)
        .map(|i| (format!("b{i}"), g(((value >> i) & 1) as u64)))
        .collect();
    let inputs: HashMap<String, F> = [
        ("challenge", challenge),
        ("i0", idx & 1),
        ("i1", (idx >> 1) & 1),
        ("idx", idx),
    ]
    .iter()
    .map(|(k, v)| ((*k).to_string(), g(*v as u64)))
    .collect();
    let wires = solve::<F>(ir, &SolveInputs { inputs: &inputs, advice_overrides: &overrides })
        .expect("the solver computes every wire from the supplied bits");
    ir.unmet::<F>(&wires)
}

/// Every (index, decomposition) pair the circuit accepts for this challenge.
fn accepted(ir: &Ir, challenge: u128) -> Vec<(u128, u128)> {
    let mut ok = Vec::new();
    for idx in 0..DOMAIN {
        for value in decompositions(challenge) {
            if attempt(ir, challenge, value, idx).is_empty() {
                ok.push((idx, value));
            }
        }
    }
    ok
}

#[test]
fn the_sound_binding_accepts_exactly_the_honest_index() {
    // The claim, by exhaustion over the prover's entire freedom: for each
    // challenge there is exactly one witness, and its index is the challenge's
    // low bits. Contrast `naive_index_binding_is_determinate_but_unsound`
    // above, where all four indices pass.
    let ir = Ir::from_json(SOUND_IR).unwrap();

    let challenges = [
        0x0123_4567_89ab_cdefu128, // an ordinary large challenge
        7,                         // small: a second decomposition exists
        4_294_967_294,             // 2^32 - 2, the largest challenge that wraps
        P - 1,                     // canonical, yet all 32 top bits are set
        0,
    ];

    for c in challenges {
        assert_eq!(
            accepted(&ir, c),
            vec![(c % DOMAIN, c)],
            "challenge {c}: expected only the honest index, on the canonical string"
        );
    }
}

#[test]
fn the_forged_index_that_satisfies_the_naive_binding_is_now_refused() {
    // The same forgery, pointed at the sound circuit. Under the naive binding
    // the prover picked `high` and reached any index; here it must produce a
    // 64-bit string, and no string congruent to the challenge has the low bits
    // it wants.
    let ir = Ir::from_json(SOUND_IR).unwrap();
    let challenge = 0x0123_4567_89ab_cdefu128;
    let honest = challenge % DOMAIN;

    for idx in 0..DOMAIN {
        if idx == honest {
            continue;
        }
        for value in decompositions(challenge) {
            let unmet = attempt(&ir, challenge, value, idx);
            assert!(!unmet.is_empty(), "index {idx} was forgeable with string {value}");
        }
    }
}

#[test]
fn the_canonicity_check_is_the_load_bearing_constraint() {
    // The wraparound case, in the sharpest form: c = 2^32 - 2, whose second
    // decomposition is the all-ones string 2^64 - 1. That string reconstructs to
    // c in the field, every bit of it is a bit, and its low bits give index 3
    // where the honest index is 2 — so a prover holding it could move the query
    // to a position of its choosing.
    //
    // Exactly one obligation stops it, and the test names it: the canonicity
    // check. If that assertion were dropped the circuit would accept two
    // indices, which is what makes this constraint load-bearing rather than
    // defensive.
    let ir = Ir::from_json(SOUND_IR).unwrap();
    let c = 4_294_967_294u128; // 2^32 - 2
    let wrapped = c + P; // = 2^64 - 1
    assert_eq!(wrapped, TWO_64 - 1);
    assert_ne!(wrapped % DOMAIN, c % DOMAIN, "the wrapped string must move the index");

    let unmet = attempt(&ir, c, wrapped, wrapped % DOMAIN);
    assert_eq!(unmet.len(), 1, "exactly one obligation should refuse this witness, got {unmet:?}");
    match &unmet[0] {
        // Every bit is a bit, the reconstruction holds, the index matches the
        // bits the prover supplied. Only canonicity objects.
        Unmet::Assertion { label, .. } => assert_eq!(label, "(ones30 * lo) == 0"),
        other => panic!("expected the canonicity assertion, got {other:?}"),
    }
}
