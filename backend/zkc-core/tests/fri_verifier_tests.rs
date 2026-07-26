//! Phase 7, O — a complete in-circuit FRI verifier for one query.
//!
//! O.1 checked the algebraic fold; O.2 proved one fold inside an outer proof.
//! This closes the arc: the *authenticity* check too. A real (tiny) FRI proof is
//! produced under a circuit-friendly hash, and for one query the in-circuit
//! verifier Merkle-verifies both openings against the committed root, folds
//! them, and checks the fold against the constant final codeword — then that
//! whole verification is itself proved and verified as an outer STARK proof.
//! Tampering an authentication path breaks it, exactly as every phase before.

use std::collections::HashMap;

use zkc_core::field::{TwoAdicField, ZkField};
use zkc_core::fri::{coset_shift, prove as fri_prove, verify as fri_verify, FriConfig};
use zkc_core::goldilocks::Goldilocks;
use zkc_core::hash::{Digest, Hasher};
use zkc_core::ir::Ir;
use zkc_core::plonkish::lower_plonkish;
use zkc_core::stark::{prove as stark_prove, verify as stark_verify};
use zkc_core::transcript::Transcript;
use zkc_core::witness::{solve, SolveInputs};

type F = Goldilocks;

fn g(v: u64) -> F {
    F::from_u64(v)
}
fn sbox(x: F) -> F {
    let x2 = x.mul(x);
    let x4 = x2.mul(x2);
    x4.mul(x2).mul(x) // x^7
}

/// The circuit-friendly hash the in-circuit verifier speaks: a single leaf [v]
/// hashes to sbox(v + 1), and two digests compress to sbox(l + 2) + sbox(r + 3).
/// These are exactly the `hash_leaf` and `compress` gadgets, so a path that
/// verifies in the tree verifies in the circuit.
#[derive(Clone)]
struct CircuitHash;
impl Hasher<F> for CircuitHash {
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

fn pow(base: F, mut e: u64) -> F {
    let (mut acc, mut b) = (F::one(), base);
    while e > 0 {
        if e & 1 == 1 {
            acc = acc.mul(b);
        }
        b = b.mul(b);
        e >>= 1;
    }
    acc
}

// The in-circuit verifier, compiled from examples/fri_verify_full.zkc.
const VERIFIER_IR: &str = r#"{"schema_version":2,"name":"FriVerifyQuery","field":"bn254","const_one_wire":0,"inputs":[{"wire":1,"name":"lo","visibility":"private","line":23},{"wire":2,"name":"hi","visibility":"private","line":24},{"wire":3,"name":"lo_sib0","visibility":"private","line":26},{"wire":4,"name":"lo_sib1","visibility":"private","line":27},{"wire":5,"name":"lo_bit0","visibility":"private","line":28},{"wire":6,"name":"lo_bit1","visibility":"private","line":29},{"wire":7,"name":"hi_sib0","visibility":"private","line":31},{"wire":8,"name":"hi_sib1","visibility":"private","line":32},{"wire":9,"name":"hi_bit0","visibility":"private","line":33},{"wire":10,"name":"hi_bit1","visibility":"private","line":34},{"wire":11,"name":"root","visibility":"private","line":36},{"wire":12,"name":"alpha","visibility":"private","line":37},{"wire":13,"name":"x","visibility":"private","line":38},{"wire":14,"name":"final0","visibility":"private","line":39},{"wire":15,"name":"final1","visibility":"private","line":40},{"wire":16,"name":"lo_leaf","visibility":"output","line":43},{"wire":17,"name":"lo_left0","visibility":"output","line":44},{"wire":18,"name":"lo_right0","visibility":"output","line":45},{"wire":19,"name":"lo_node0","visibility":"output","line":46},{"wire":20,"name":"lo_left1","visibility":"output","line":47},{"wire":21,"name":"lo_right1","visibility":"output","line":48},{"wire":22,"name":"lo_root","visibility":"output","line":49},{"wire":23,"name":"hi_leaf","visibility":"output","line":50},{"wire":24,"name":"hi_left0","visibility":"output","line":51},{"wire":25,"name":"hi_right0","visibility":"output","line":52},{"wire":26,"name":"hi_node0","visibility":"output","line":53},{"wire":27,"name":"hi_left1","visibility":"output","line":54},{"wire":28,"name":"hi_right1","visibility":"output","line":55},{"wire":29,"name":"hi_root","visibility":"output","line":56},{"wire":30,"name":"folded","visibility":"output","line":57},{"wire":31,"name":"accepted","visibility":"output","line":58}],"nodes":[{"wire":32,"advice_derived":false,"line":6,"op":"const","value":"1"},{"wire":33,"advice_derived":false,"line":6,"op":"add","args":[1,32]},{"wire":34,"advice_derived":false,"line":7,"op":"mul","args":[33,33]},{"wire":35,"advice_derived":false,"line":8,"op":"mul","args":[34,34]},{"wire":36,"advice_derived":false,"line":9,"op":"mul","args":[35,34]},{"wire":37,"advice_derived":false,"line":10,"op":"mul","args":[36,33]},{"wire":38,"advice_derived":false,"line":7,"op":"sub","args":[32,5]},{"wire":39,"advice_derived":false,"line":7,"op":"mul","args":[5,38]},{"wire":40,"advice_derived":false,"line":7,"op":"const","value":"0"},{"wire":41,"advice_derived":false,"line":8,"op":"sub","args":[3,16]},{"wire":42,"advice_derived":false,"line":8,"op":"mul","args":[5,41]},{"wire":43,"advice_derived":false,"line":8,"op":"add","args":[16,42]},{"wire":44,"advice_derived":false,"line":8,"op":"sub","args":[16,3]},{"wire":45,"advice_derived":false,"line":8,"op":"mul","args":[5,44]},{"wire":46,"advice_derived":false,"line":8,"op":"add","args":[3,45]},{"wire":47,"advice_derived":false,"line":7,"op":"const","value":"2"},{"wire":48,"advice_derived":false,"line":7,"op":"add","args":[17,47]},{"wire":49,"advice_derived":false,"line":8,"op":"mul","args":[48,48]},{"wire":50,"advice_derived":false,"line":9,"op":"mul","args":[49,49]},{"wire":51,"advice_derived":false,"line":10,"op":"mul","args":[50,49]},{"wire":52,"advice_derived":false,"line":11,"op":"mul","args":[51,48]},{"wire":53,"advice_derived":false,"line":12,"op":"const","value":"3"},{"wire":54,"advice_derived":false,"line":12,"op":"add","args":[18,53]},{"wire":55,"advice_derived":false,"line":13,"op":"mul","args":[54,54]},{"wire":56,"advice_derived":false,"line":14,"op":"mul","args":[55,55]},{"wire":57,"advice_derived":false,"line":15,"op":"mul","args":[56,55]},{"wire":58,"advice_derived":false,"line":16,"op":"mul","args":[57,54]},{"wire":59,"advice_derived":false,"line":17,"op":"add","args":[52,58]},{"wire":60,"advice_derived":false,"line":7,"op":"sub","args":[32,6]},{"wire":61,"advice_derived":false,"line":7,"op":"mul","args":[6,60]},{"wire":62,"advice_derived":false,"line":8,"op":"sub","args":[4,19]},{"wire":63,"advice_derived":false,"line":8,"op":"mul","args":[6,62]},{"wire":64,"advice_derived":false,"line":8,"op":"add","args":[19,63]},{"wire":65,"advice_derived":false,"line":8,"op":"sub","args":[19,4]},{"wire":66,"advice_derived":false,"line":8,"op":"mul","args":[6,65]},{"wire":67,"advice_derived":false,"line":8,"op":"add","args":[4,66]},{"wire":68,"advice_derived":false,"line":7,"op":"add","args":[20,47]},{"wire":69,"advice_derived":false,"line":8,"op":"mul","args":[68,68]},{"wire":70,"advice_derived":false,"line":9,"op":"mul","args":[69,69]},{"wire":71,"advice_derived":false,"line":10,"op":"mul","args":[70,69]},{"wire":72,"advice_derived":false,"line":11,"op":"mul","args":[71,68]},{"wire":73,"advice_derived":false,"line":12,"op":"add","args":[21,53]},{"wire":74,"advice_derived":false,"line":13,"op":"mul","args":[73,73]},{"wire":75,"advice_derived":false,"line":14,"op":"mul","args":[74,74]},{"wire":76,"advice_derived":false,"line":15,"op":"mul","args":[75,74]},{"wire":77,"advice_derived":false,"line":16,"op":"mul","args":[76,73]},{"wire":78,"advice_derived":false,"line":17,"op":"add","args":[72,77]},{"wire":79,"advice_derived":false,"line":6,"op":"add","args":[2,32]},{"wire":80,"advice_derived":false,"line":7,"op":"mul","args":[79,79]},{"wire":81,"advice_derived":false,"line":8,"op":"mul","args":[80,80]},{"wire":82,"advice_derived":false,"line":9,"op":"mul","args":[81,80]},{"wire":83,"advice_derived":false,"line":10,"op":"mul","args":[82,79]},{"wire":84,"advice_derived":false,"line":7,"op":"sub","args":[32,9]},{"wire":85,"advice_derived":false,"line":7,"op":"mul","args":[9,84]},{"wire":86,"advice_derived":false,"line":8,"op":"sub","args":[7,23]},{"wire":87,"advice_derived":false,"line":8,"op":"mul","args":[9,86]},{"wire":88,"advice_derived":false,"line":8,"op":"add","args":[23,87]},{"wire":89,"advice_derived":false,"line":8,"op":"sub","args":[23,7]},{"wire":90,"advice_derived":false,"line":8,"op":"mul","args":[9,89]},{"wire":91,"advice_derived":false,"line":8,"op":"add","args":[7,90]},{"wire":92,"advice_derived":false,"line":7,"op":"add","args":[24,47]},{"wire":93,"advice_derived":false,"line":8,"op":"mul","args":[92,92]},{"wire":94,"advice_derived":false,"line":9,"op":"mul","args":[93,93]},{"wire":95,"advice_derived":false,"line":10,"op":"mul","args":[94,93]},{"wire":96,"advice_derived":false,"line":11,"op":"mul","args":[95,92]},{"wire":97,"advice_derived":false,"line":12,"op":"add","args":[25,53]},{"wire":98,"advice_derived":false,"line":13,"op":"mul","args":[97,97]},{"wire":99,"advice_derived":false,"line":14,"op":"mul","args":[98,98]},{"wire":100,"advice_derived":false,"line":15,"op":"mul","args":[99,98]},{"wire":101,"advice_derived":false,"line":16,"op":"mul","args":[100,97]},{"wire":102,"advice_derived":false,"line":17,"op":"add","args":[96,101]},{"wire":103,"advice_derived":false,"line":7,"op":"sub","args":[32,10]},{"wire":104,"advice_derived":false,"line":7,"op":"mul","args":[10,103]},{"wire":105,"advice_derived":false,"line":8,"op":"sub","args":[8,26]},{"wire":106,"advice_derived":false,"line":8,"op":"mul","args":[10,105]},{"wire":107,"advice_derived":false,"line":8,"op":"add","args":[26,106]},{"wire":108,"advice_derived":false,"line":8,"op":"sub","args":[26,8]},{"wire":109,"advice_derived":false,"line":8,"op":"mul","args":[10,108]},{"wire":110,"advice_derived":false,"line":8,"op":"add","args":[8,109]},{"wire":111,"advice_derived":false,"line":7,"op":"add","args":[27,47]},{"wire":112,"advice_derived":false,"line":8,"op":"mul","args":[111,111]},{"wire":113,"advice_derived":false,"line":9,"op":"mul","args":[112,112]},{"wire":114,"advice_derived":false,"line":10,"op":"mul","args":[113,112]},{"wire":115,"advice_derived":false,"line":11,"op":"mul","args":[114,111]},{"wire":116,"advice_derived":false,"line":12,"op":"add","args":[28,53]},{"wire":117,"advice_derived":false,"line":13,"op":"mul","args":[116,116]},{"wire":118,"advice_derived":false,"line":14,"op":"mul","args":[117,117]},{"wire":119,"advice_derived":false,"line":15,"op":"mul","args":[118,117]},{"wire":120,"advice_derived":false,"line":16,"op":"mul","args":[119,116]},{"wire":121,"advice_derived":false,"line":17,"op":"add","args":[115,120]},{"wire":122,"advice_derived":false,"line":16,"op":"add","args":[13,13]},{"wire":123,"advice_derived":true,"op":"hint","hint":"inv","name":"inv2x","gadget":"fri_fold","line":16,"args":[122]},{"wire":124,"advice_derived":true,"line":17,"op":"mul","args":[122,123]},{"wire":125,"advice_derived":false,"line":18,"op":"add","args":[1,2]},{"wire":126,"advice_derived":false,"line":18,"op":"mul","args":[13,125]},{"wire":127,"advice_derived":false,"line":18,"op":"sub","args":[1,2]},{"wire":128,"advice_derived":false,"line":18,"op":"mul","args":[12,127]},{"wire":129,"advice_derived":false,"line":18,"op":"add","args":[126,128]},{"wire":130,"advice_derived":true,"line":19,"op":"mul","args":[123,129]}],"assertions":[{"lhs":16,"rhs":37,"label":"h == (a6 * a)","line":10},{"lhs":39,"rhs":40,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":17,"rhs":43,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":39,"rhs":40,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":18,"rhs":46,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":19,"rhs":59,"label":"h == (sl + sr)","line":17},{"lhs":61,"rhs":40,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":20,"rhs":64,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":61,"rhs":40,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":21,"rhs":67,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":22,"rhs":78,"label":"h == (sl + sr)","line":17},{"lhs":22,"rhs":11,"label":"lo_root == root","line":68},{"lhs":23,"rhs":83,"label":"h == (a6 * a)","line":10},{"lhs":85,"rhs":40,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":24,"rhs":88,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":85,"rhs":40,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":25,"rhs":91,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":26,"rhs":102,"label":"h == (sl + sr)","line":17},{"lhs":104,"rhs":40,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":27,"rhs":107,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":104,"rhs":40,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":28,"rhs":110,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":29,"rhs":121,"label":"h == (sl + sr)","line":17},{"lhs":29,"rhs":11,"label":"hi_root == root","line":78},{"lhs":124,"rhs":32,"label":"((x + x) * inv2x) == 1","line":17},{"lhs":30,"rhs":130,"label":"folded == (inv2x * rhs)","line":19},{"lhs":30,"rhs":14,"label":"folded == final0","line":82},{"lhs":14,"rhs":15,"label":"final0 == final1","line":83},{"lhs":31,"rhs":32,"label":"accepted == 1","line":85}],"determinacy":{"proved":true,"targets":["lo_leaf","lo_left0","lo_right0","lo_node0","lo_left1","lo_right1","lo_root","hi_leaf","hi_left0","hi_right0","hi_node0","hi_left1","hi_right1","hi_root","folded","accepted"],"branches":[["x == 0"],["x != 0"]]}}"#;

/// A real one-round FRI proof and the verifier inputs for its first query.
fn proof_and_query_inputs() -> (HashMap<String, F>, FriConfig) {
    let degree_bound = 2usize;
    let config = FriConfig { blowup: 2, num_queries: 1 };
    let coeffs: Vec<F> = vec![g(7), g(3)]; // degree < 2

    let mut prover_t = Transcript::<_, CircuitHash>::new(&[g(1)]);
    let inner = fri_prove(&coeffs, degree_bound, &config, &mut prover_t);
    let mut verifier_t = Transcript::<_, CircuitHash>::new(&[g(1)]);
    assert!(
        fri_verify(&inner, degree_bound, &config, &mut verifier_t).is_ok(),
        "the inner FRI proof must verify"
    );

    // Replay for the folding challenge.
    let mut replay = Transcript::<_, CircuitHash>::new(&[g(1)]);
    let mut alphas = Vec::new();
    for root in &inner.roots {
        replay.absorb_digest(root);
        alphas.push(replay.challenge());
    }

    let query = &inner.queries[0];
    let layer = &query.layers[0];
    let domain = inner.domain_size;
    let half0 = domain / 2;
    let lo0 = query.index % half0;
    let gen = F::two_adic_generator(domain.trailing_zeros());
    let x = coset_shift::<F>().mul(pow(gen, lo0 as u64));

    let bit = |idx: usize, level: u32| g(((idx >> level) & 1) as u64);
    let sib = |op: &zkc_core::merkle::Opening<F>, level: usize| op.siblings[level].0[0];

    // The prover computes the honest witness — the hashes up each path and the
    // fold — with the same arithmetic the gadgets constrain. The circuit then
    // checks it: a wrong value fails a hash or Merkle assertion.
    let hash_leaf = |v: F| sbox(v.add(g(1)));
    let compress = |l: F, r: F| sbox(l.add(g(2))).add(sbox(r.add(g(3))));
    let mux = |sel: F, a: F, b: F| if sel == g(1) { a } else { b };
    let fold = |p: F, m: F, beta: F, xx: F| {
        xx.add(xx).inverse().unwrap().mul(xx.mul(p.add(m)).add(beta.mul(p.sub(m))))
    };

    let (lo, hi) = (layer.lo, layer.hi);
    let (lb0, lb1) = (bit(layer.lo_proof.index, 0), bit(layer.lo_proof.index, 1));
    let (ls0, ls1) = (sib(&layer.lo_proof, 0), sib(&layer.lo_proof, 1));
    let (hb0, hb1) = (bit(layer.hi_proof.index, 0), bit(layer.hi_proof.index, 1));
    let (hs0, hs1) = (sib(&layer.hi_proof, 0), sib(&layer.hi_proof, 1));
    let alpha = alphas[0];
    let (final0, final1) = (inner.final_poly[0], inner.final_poly[1]);
    let root = inner.roots[0].0[0];

    let lo_leaf = hash_leaf(lo);
    let lo_left0 = mux(lb0, ls0, lo_leaf);
    let lo_right0 = mux(lb0, lo_leaf, ls0);
    let lo_node0 = compress(lo_left0, lo_right0);
    let lo_left1 = mux(lb1, ls1, lo_node0);
    let lo_right1 = mux(lb1, lo_node0, ls1);
    let lo_root = compress(lo_left1, lo_right1);

    let hi_leaf = hash_leaf(hi);
    let hi_left0 = mux(hb0, hs0, hi_leaf);
    let hi_right0 = mux(hb0, hi_leaf, hs0);
    let hi_node0 = compress(hi_left0, hi_right0);
    let hi_left1 = mux(hb1, hs1, hi_node0);
    let hi_right1 = mux(hb1, hi_node0, hs1);
    let hi_root = compress(hi_left1, hi_right1);

    let folded = fold(lo, hi, alpha, x);

    let inputs: HashMap<String, F> = [
        ("lo", lo), ("hi", hi),
        ("lo_sib0", ls0), ("lo_sib1", ls1), ("lo_bit0", lb0), ("lo_bit1", lb1),
        ("hi_sib0", hs0), ("hi_sib1", hs1), ("hi_bit0", hb0), ("hi_bit1", hb1),
        ("root", root), ("alpha", alpha), ("x", x),
        ("final0", final0), ("final1", final1),
        // prover-supplied intermediate results the circuit verifies:
        ("lo_leaf", lo_leaf), ("lo_left0", lo_left0), ("lo_right0", lo_right0),
        ("lo_node0", lo_node0), ("lo_left1", lo_left1), ("lo_right1", lo_right1),
        ("lo_root", lo_root),
        ("hi_leaf", hi_leaf), ("hi_left0", hi_left0), ("hi_right0", hi_right0),
        ("hi_node0", hi_node0), ("hi_left1", hi_left1), ("hi_right1", hi_right1),
        ("hi_root", hi_root),
        ("folded", folded), ("accepted", g(1)),
    ]
    .iter()
    .map(|(k, v)| ((*k).to_string(), *v))
    .collect();

    (inputs, config)
}

#[test]
fn a_full_fri_query_is_verified_inside_an_outer_proof() {
    let (inputs, _config) = proof_and_query_inputs();
    let ir = Ir::from_json(VERIFIER_IR).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
    )
    .unwrap();
    let vcircuit = lower_plonkish::<F>(&ir).unwrap();

    // The complete verification — Merkle paths, fold, final check — is satisfied.
    assert!(
        vcircuit.is_satisfied(&vcircuit.assignment(&wires)),
        "the in-circuit verifier must accept a real, honest query"
    );

    // And proving it yields an outer proof that verifies: recursion over the
    // whole query, authentication paths included.
    let config = FriConfig::default();
    let outer = stark_prove::<F, CircuitHash>(&vcircuit, &wires, &config);
    assert!(
        stark_verify::<F, CircuitHash>(&vcircuit, &outer, &config).is_ok(),
        "the outer proof over the full query must verify"
    );
}

#[test]
fn a_tampered_authentication_path_breaks_the_verifier() {
    let (mut inputs, _config) = proof_and_query_inputs();
    let ir = Ir::from_json(VERIFIER_IR).unwrap();
    let vcircuit = lower_plonkish::<F>(&ir).unwrap();

    // Tamper one sibling on lo's authentication path: the recomputed root no
    // longer matches, so the Merkle check — and the whole verifier — rejects it.
    let sib = inputs.get_mut("lo_sib0").unwrap();
    *sib = sib.add(F::one());

    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
    )
    .unwrap();
    assert!(
        !vcircuit.is_satisfied(&vcircuit.assignment(&wires)),
        "a tampered authentication path must be rejected before proving"
    );

    let config = FriConfig::default();
    let forced = stark_prove::<F, CircuitHash>(&vcircuit, &wires, &config);
    assert!(
        stark_verify::<F, CircuitHash>(&vcircuit, &forced, &config).is_err(),
        "a forced outer proof over a tampered path must not verify"
    );
}

// --- In-circuit Fiat-Shamir --------------------------------------------------
//
// The verifier above trusted the fold challenge as an input. Here it is derived
// in-circuit from the layer commitment, so the prover cannot choose it after
// committing — the soundness Fiat-Shamir exists to provide, enforced by the
// circuit. For the transcript state [seed, root] and the circuit-friendly hash,
// the round-0 challenge is sbox(seed + root + 6); the test checks that against
// the real transcript before proving the whole verification.

const VERIFIER_FS_IR: &str = r#"{"schema_version":2,"name":"FriVerifyFS","field":"bn254","const_one_wire":0,"inputs":[{"wire":1,"name":"lo","visibility":"private","line":17},{"wire":2,"name":"hi","visibility":"private","line":18},{"wire":3,"name":"lo_sib0","visibility":"private","line":19},{"wire":4,"name":"lo_sib1","visibility":"private","line":20},{"wire":5,"name":"lo_bit0","visibility":"private","line":21},{"wire":6,"name":"lo_bit1","visibility":"private","line":22},{"wire":7,"name":"hi_sib0","visibility":"private","line":23},{"wire":8,"name":"hi_sib1","visibility":"private","line":24},{"wire":9,"name":"hi_bit0","visibility":"private","line":25},{"wire":10,"name":"hi_bit1","visibility":"private","line":26},{"wire":11,"name":"root","visibility":"private","line":27},{"wire":12,"name":"seed","visibility":"private","line":28},{"wire":13,"name":"x","visibility":"private","line":29},{"wire":14,"name":"final0","visibility":"private","line":30},{"wire":15,"name":"final1","visibility":"private","line":31},{"wire":16,"name":"lo_leaf","visibility":"output","line":33},{"wire":17,"name":"lo_left0","visibility":"output","line":34},{"wire":18,"name":"lo_right0","visibility":"output","line":35},{"wire":19,"name":"lo_node0","visibility":"output","line":36},{"wire":20,"name":"lo_left1","visibility":"output","line":37},{"wire":21,"name":"lo_right1","visibility":"output","line":38},{"wire":22,"name":"lo_root","visibility":"output","line":39},{"wire":23,"name":"hi_leaf","visibility":"output","line":40},{"wire":24,"name":"hi_left0","visibility":"output","line":41},{"wire":25,"name":"hi_right0","visibility":"output","line":42},{"wire":26,"name":"hi_node0","visibility":"output","line":43},{"wire":27,"name":"hi_left1","visibility":"output","line":44},{"wire":28,"name":"hi_right1","visibility":"output","line":45},{"wire":29,"name":"hi_root","visibility":"output","line":46},{"wire":30,"name":"alpha","visibility":"output","line":47},{"wire":31,"name":"folded","visibility":"output","line":48},{"wire":32,"name":"accepted","visibility":"output","line":49}],"nodes":[{"wire":33,"advice_derived":false,"line":6,"op":"const","value":"1"},{"wire":34,"advice_derived":false,"line":6,"op":"add","args":[1,33]},{"wire":35,"advice_derived":false,"line":7,"op":"mul","args":[34,34]},{"wire":36,"advice_derived":false,"line":8,"op":"mul","args":[35,35]},{"wire":37,"advice_derived":false,"line":9,"op":"mul","args":[36,35]},{"wire":38,"advice_derived":false,"line":10,"op":"mul","args":[37,34]},{"wire":39,"advice_derived":false,"line":7,"op":"sub","args":[33,5]},{"wire":40,"advice_derived":false,"line":7,"op":"mul","args":[5,39]},{"wire":41,"advice_derived":false,"line":7,"op":"const","value":"0"},{"wire":42,"advice_derived":false,"line":8,"op":"sub","args":[3,16]},{"wire":43,"advice_derived":false,"line":8,"op":"mul","args":[5,42]},{"wire":44,"advice_derived":false,"line":8,"op":"add","args":[16,43]},{"wire":45,"advice_derived":false,"line":8,"op":"sub","args":[16,3]},{"wire":46,"advice_derived":false,"line":8,"op":"mul","args":[5,45]},{"wire":47,"advice_derived":false,"line":8,"op":"add","args":[3,46]},{"wire":48,"advice_derived":false,"line":7,"op":"const","value":"2"},{"wire":49,"advice_derived":false,"line":7,"op":"add","args":[17,48]},{"wire":50,"advice_derived":false,"line":8,"op":"mul","args":[49,49]},{"wire":51,"advice_derived":false,"line":9,"op":"mul","args":[50,50]},{"wire":52,"advice_derived":false,"line":10,"op":"mul","args":[51,50]},{"wire":53,"advice_derived":false,"line":11,"op":"mul","args":[52,49]},{"wire":54,"advice_derived":false,"line":12,"op":"const","value":"3"},{"wire":55,"advice_derived":false,"line":12,"op":"add","args":[18,54]},{"wire":56,"advice_derived":false,"line":13,"op":"mul","args":[55,55]},{"wire":57,"advice_derived":false,"line":14,"op":"mul","args":[56,56]},{"wire":58,"advice_derived":false,"line":15,"op":"mul","args":[57,56]},{"wire":59,"advice_derived":false,"line":16,"op":"mul","args":[58,55]},{"wire":60,"advice_derived":false,"line":17,"op":"add","args":[53,59]},{"wire":61,"advice_derived":false,"line":7,"op":"sub","args":[33,6]},{"wire":62,"advice_derived":false,"line":7,"op":"mul","args":[6,61]},{"wire":63,"advice_derived":false,"line":8,"op":"sub","args":[4,19]},{"wire":64,"advice_derived":false,"line":8,"op":"mul","args":[6,63]},{"wire":65,"advice_derived":false,"line":8,"op":"add","args":[19,64]},{"wire":66,"advice_derived":false,"line":8,"op":"sub","args":[19,4]},{"wire":67,"advice_derived":false,"line":8,"op":"mul","args":[6,66]},{"wire":68,"advice_derived":false,"line":8,"op":"add","args":[4,67]},{"wire":69,"advice_derived":false,"line":7,"op":"add","args":[20,48]},{"wire":70,"advice_derived":false,"line":8,"op":"mul","args":[69,69]},{"wire":71,"advice_derived":false,"line":9,"op":"mul","args":[70,70]},{"wire":72,"advice_derived":false,"line":10,"op":"mul","args":[71,70]},{"wire":73,"advice_derived":false,"line":11,"op":"mul","args":[72,69]},{"wire":74,"advice_derived":false,"line":12,"op":"add","args":[21,54]},{"wire":75,"advice_derived":false,"line":13,"op":"mul","args":[74,74]},{"wire":76,"advice_derived":false,"line":14,"op":"mul","args":[75,75]},{"wire":77,"advice_derived":false,"line":15,"op":"mul","args":[76,75]},{"wire":78,"advice_derived":false,"line":16,"op":"mul","args":[77,74]},{"wire":79,"advice_derived":false,"line":17,"op":"add","args":[73,78]},{"wire":80,"advice_derived":false,"line":6,"op":"add","args":[2,33]},{"wire":81,"advice_derived":false,"line":7,"op":"mul","args":[80,80]},{"wire":82,"advice_derived":false,"line":8,"op":"mul","args":[81,81]},{"wire":83,"advice_derived":false,"line":9,"op":"mul","args":[82,81]},{"wire":84,"advice_derived":false,"line":10,"op":"mul","args":[83,80]},{"wire":85,"advice_derived":false,"line":7,"op":"sub","args":[33,9]},{"wire":86,"advice_derived":false,"line":7,"op":"mul","args":[9,85]},{"wire":87,"advice_derived":false,"line":8,"op":"sub","args":[7,23]},{"wire":88,"advice_derived":false,"line":8,"op":"mul","args":[9,87]},{"wire":89,"advice_derived":false,"line":8,"op":"add","args":[23,88]},{"wire":90,"advice_derived":false,"line":8,"op":"sub","args":[23,7]},{"wire":91,"advice_derived":false,"line":8,"op":"mul","args":[9,90]},{"wire":92,"advice_derived":false,"line":8,"op":"add","args":[7,91]},{"wire":93,"advice_derived":false,"line":7,"op":"add","args":[24,48]},{"wire":94,"advice_derived":false,"line":8,"op":"mul","args":[93,93]},{"wire":95,"advice_derived":false,"line":9,"op":"mul","args":[94,94]},{"wire":96,"advice_derived":false,"line":10,"op":"mul","args":[95,94]},{"wire":97,"advice_derived":false,"line":11,"op":"mul","args":[96,93]},{"wire":98,"advice_derived":false,"line":12,"op":"add","args":[25,54]},{"wire":99,"advice_derived":false,"line":13,"op":"mul","args":[98,98]},{"wire":100,"advice_derived":false,"line":14,"op":"mul","args":[99,99]},{"wire":101,"advice_derived":false,"line":15,"op":"mul","args":[100,99]},{"wire":102,"advice_derived":false,"line":16,"op":"mul","args":[101,98]},{"wire":103,"advice_derived":false,"line":17,"op":"add","args":[97,102]},{"wire":104,"advice_derived":false,"line":7,"op":"sub","args":[33,10]},{"wire":105,"advice_derived":false,"line":7,"op":"mul","args":[10,104]},{"wire":106,"advice_derived":false,"line":8,"op":"sub","args":[8,26]},{"wire":107,"advice_derived":false,"line":8,"op":"mul","args":[10,106]},{"wire":108,"advice_derived":false,"line":8,"op":"add","args":[26,107]},{"wire":109,"advice_derived":false,"line":8,"op":"sub","args":[26,8]},{"wire":110,"advice_derived":false,"line":8,"op":"mul","args":[10,109]},{"wire":111,"advice_derived":false,"line":8,"op":"add","args":[8,110]},{"wire":112,"advice_derived":false,"line":7,"op":"add","args":[27,48]},{"wire":113,"advice_derived":false,"line":8,"op":"mul","args":[112,112]},{"wire":114,"advice_derived":false,"line":9,"op":"mul","args":[113,113]},{"wire":115,"advice_derived":false,"line":10,"op":"mul","args":[114,113]},{"wire":116,"advice_derived":false,"line":11,"op":"mul","args":[115,112]},{"wire":117,"advice_derived":false,"line":12,"op":"add","args":[28,54]},{"wire":118,"advice_derived":false,"line":13,"op":"mul","args":[117,117]},{"wire":119,"advice_derived":false,"line":14,"op":"mul","args":[118,118]},{"wire":120,"advice_derived":false,"line":15,"op":"mul","args":[119,118]},{"wire":121,"advice_derived":false,"line":16,"op":"mul","args":[120,117]},{"wire":122,"advice_derived":false,"line":17,"op":"add","args":[116,121]},{"wire":123,"advice_derived":false,"line":13,"op":"add","args":[12,11]},{"wire":124,"advice_derived":false,"line":13,"op":"const","value":"6"},{"wire":125,"advice_derived":false,"line":13,"op":"add","args":[123,124]},{"wire":126,"advice_derived":false,"line":14,"op":"mul","args":[125,125]},{"wire":127,"advice_derived":false,"line":15,"op":"mul","args":[126,126]},{"wire":128,"advice_derived":false,"line":16,"op":"mul","args":[127,126]},{"wire":129,"advice_derived":false,"line":17,"op":"mul","args":[128,125]},{"wire":130,"advice_derived":false,"line":16,"op":"add","args":[13,13]},{"wire":131,"advice_derived":true,"op":"hint","hint":"inv","name":"inv2x","gadget":"fri_fold","line":16,"args":[130]},{"wire":132,"advice_derived":true,"line":17,"op":"mul","args":[130,131]},{"wire":133,"advice_derived":false,"line":18,"op":"add","args":[1,2]},{"wire":134,"advice_derived":false,"line":18,"op":"mul","args":[13,133]},{"wire":135,"advice_derived":false,"line":18,"op":"sub","args":[1,2]},{"wire":136,"advice_derived":false,"line":18,"op":"mul","args":[30,135]},{"wire":137,"advice_derived":false,"line":18,"op":"add","args":[134,136]},{"wire":138,"advice_derived":true,"line":19,"op":"mul","args":[131,137]}],"assertions":[{"lhs":16,"rhs":38,"label":"h == (a6 * a)","line":10},{"lhs":40,"rhs":41,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":17,"rhs":44,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":40,"rhs":41,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":18,"rhs":47,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":19,"rhs":60,"label":"h == (sl + sr)","line":17},{"lhs":62,"rhs":41,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":20,"rhs":65,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":62,"rhs":41,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":21,"rhs":68,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":22,"rhs":79,"label":"h == (sl + sr)","line":17},{"lhs":22,"rhs":11,"label":"lo_root == root","line":59},{"lhs":23,"rhs":84,"label":"h == (a6 * a)","line":10},{"lhs":86,"rhs":41,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":24,"rhs":89,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":86,"rhs":41,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":25,"rhs":92,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":26,"rhs":103,"label":"h == (sl + sr)","line":17},{"lhs":105,"rhs":41,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":27,"rhs":108,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":105,"rhs":41,"label":"(sel * (1 - sel)) == 0","line":7},{"lhs":28,"rhs":111,"label":"out == (b + (sel * (a - b)))","line":8},{"lhs":29,"rhs":122,"label":"h == (sl + sr)","line":17},{"lhs":29,"rhs":11,"label":"hi_root == root","line":69},{"lhs":30,"rhs":129,"label":"alpha == (a6 * a)","line":17},{"lhs":132,"rhs":33,"label":"((x + x) * inv2x) == 1","line":17},{"lhs":31,"rhs":138,"label":"folded == (inv2x * rhs)","line":19},{"lhs":31,"rhs":14,"label":"folded == final0","line":76},{"lhs":14,"rhs":15,"label":"final0 == final1","line":77},{"lhs":32,"rhs":33,"label":"accepted == 1","line":79}],"determinacy":{"proved":true,"targets":["lo_leaf","lo_left0","lo_right0","lo_node0","lo_left1","lo_right1","lo_root","hi_leaf","hi_left0","hi_right0","hi_node0","hi_left1","hi_right1","hi_root","alpha","folded","accepted"],"branches":[["x == 0"],["x != 0"]]}}"#;

fn fs_query_inputs() -> (HashMap<String, F>, F, F) {
    let degree_bound = 2usize;
    let config = FriConfig { blowup: 2, num_queries: 1 };
    let coeffs: Vec<F> = vec![g(7), g(3)];
    let seed = g(1);

    let mut prover_t = Transcript::<_, CircuitHash>::new(&[seed]);
    let inner = fri_prove(&coeffs, degree_bound, &config, &mut prover_t);
    let mut verifier_t = Transcript::<_, CircuitHash>::new(&[seed]);
    assert!(fri_verify(&inner, degree_bound, &config, &mut verifier_t).is_ok());

    let mut replay = Transcript::<_, CircuitHash>::new(&[seed]);
    let mut alphas = Vec::new();
    for root in &inner.roots {
        replay.absorb_digest(root);
        alphas.push(replay.challenge());
    }

    let query = &inner.queries[0];
    let layer = &query.layers[0];
    let domain = inner.domain_size;
    let half0 = domain / 2;
    let lo0 = query.index % half0;
    let gen = F::two_adic_generator(domain.trailing_zeros());
    let x = coset_shift::<F>().mul(pow(gen, lo0 as u64));
    let root = inner.roots[0].0[0];

    // Fiat-Shamir, in the field: derive the challenge from seed and root, and
    // confirm it is exactly what the transcript produced.
    let alpha_derived = sbox(seed.add(root).add(g(6)));
    assert_eq!(alpha_derived, alphas[0], "in-circuit Fiat-Shamir must match the transcript");

    let bit = |idx: usize, level: u32| g(((idx >> level) & 1) as u64);
    let sib = |op: &zkc_core::merkle::Opening<F>, level: usize| op.siblings[level].0[0];
    let hash_leaf = |v: F| sbox(v.add(g(1)));
    let compress = |l: F, r: F| sbox(l.add(g(2))).add(sbox(r.add(g(3))));
    let mux = |sel: F, a: F, b: F| if sel == g(1) { a } else { b };
    let fold = |p: F, m: F, beta: F, xx: F| {
        xx.add(xx).inverse().unwrap().mul(xx.mul(p.add(m)).add(beta.mul(p.sub(m))))
    };

    let (lo, hi) = (layer.lo, layer.hi);
    let (lb0, lb1) = (bit(layer.lo_proof.index, 0), bit(layer.lo_proof.index, 1));
    let (ls0, ls1) = (sib(&layer.lo_proof, 0), sib(&layer.lo_proof, 1));
    let (hb0, hb1) = (bit(layer.hi_proof.index, 0), bit(layer.hi_proof.index, 1));
    let (hs0, hs1) = (sib(&layer.hi_proof, 0), sib(&layer.hi_proof, 1));
    let (final0, final1) = (inner.final_poly[0], inner.final_poly[1]);

    let lo_leaf = hash_leaf(lo);
    let lo_left0 = mux(lb0, ls0, lo_leaf);
    let lo_right0 = mux(lb0, lo_leaf, ls0);
    let lo_node0 = compress(lo_left0, lo_right0);
    let lo_left1 = mux(lb1, ls1, lo_node0);
    let lo_right1 = mux(lb1, lo_node0, ls1);
    let lo_root = compress(lo_left1, lo_right1);
    let hi_leaf = hash_leaf(hi);
    let hi_left0 = mux(hb0, hs0, hi_leaf);
    let hi_right0 = mux(hb0, hi_leaf, hs0);
    let hi_node0 = compress(hi_left0, hi_right0);
    let hi_left1 = mux(hb1, hs1, hi_node0);
    let hi_right1 = mux(hb1, hi_node0, hs1);
    let hi_root = compress(hi_left1, hi_right1);
    let folded = fold(lo, hi, alpha_derived, x);

    let inputs: HashMap<String, F> = [
        ("lo", lo), ("hi", hi),
        ("lo_sib0", ls0), ("lo_sib1", ls1), ("lo_bit0", lb0), ("lo_bit1", lb1),
        ("hi_sib0", hs0), ("hi_sib1", hs1), ("hi_bit0", hb0), ("hi_bit1", hb1),
        ("root", root), ("seed", seed), ("x", x),
        ("final0", final0), ("final1", final1),
        ("lo_leaf", lo_leaf), ("lo_left0", lo_left0), ("lo_right0", lo_right0),
        ("lo_node0", lo_node0), ("lo_left1", lo_left1), ("lo_right1", lo_right1),
        ("lo_root", lo_root),
        ("hi_leaf", hi_leaf), ("hi_left0", hi_left0), ("hi_right0", hi_right0),
        ("hi_node0", hi_node0), ("hi_left1", hi_left1), ("hi_right1", hi_right1),
        ("hi_root", hi_root),
        ("alpha", alpha_derived), ("folded", folded), ("accepted", g(1)),
    ]
    .iter()
    .map(|(k, v)| ((*k).to_string(), *v))
    .collect();

    (inputs, root, seed)
}

#[test]
fn the_fold_challenge_is_derived_in_circuit_and_the_verifier_proves() {
    let (inputs, _root, _seed) = fs_query_inputs();
    let ir = Ir::from_json(VERIFIER_FS_IR).unwrap();
    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
    )
    .unwrap();
    let vcircuit = lower_plonkish::<F>(&ir).unwrap();
    assert!(
        vcircuit.is_satisfied(&vcircuit.assignment(&wires)),
        "the verifier, deriving its own challenge, must accept the honest query"
    );

    let config = FriConfig::default();
    let outer = stark_prove::<F, CircuitHash>(&vcircuit, &wires, &config);
    assert!(
        stark_verify::<F, CircuitHash>(&vcircuit, &outer, &config).is_ok(),
        "the outer proof, with in-circuit Fiat-Shamir, must verify"
    );
}

#[test]
fn a_challenge_not_bound_to_the_commitment_is_rejected() {
    // The point of in-circuit Fiat-Shamir: alpha must equal fs_challenge(seed,
    // root). Supplying any other value fails the derivation constraint, so a
    // prover cannot pick a convenient challenge after committing.
    let (mut inputs, root, seed) = fs_query_inputs();
    let ir = Ir::from_json(VERIFIER_FS_IR).unwrap();
    let vcircuit = lower_plonkish::<F>(&ir).unwrap();

    // Swap in a different challenge (and keep everything else as computed).
    let honest_alpha = sbox(seed.add(root).add(g(6)));
    *inputs.get_mut("alpha").unwrap() = honest_alpha.add(F::one());

    let wires = solve::<F>(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &HashMap::new() },
    )
    .unwrap();
    assert!(
        !vcircuit.is_satisfied(&vcircuit.assignment(&wires)),
        "a challenge not derived from the commitment must be rejected"
    );
}
