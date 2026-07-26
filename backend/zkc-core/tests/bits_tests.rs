//! The `bits` decomposition hint — end-to-end. The frontend proves these
//! circuits determinate (the `closeBits` rule certifies that bits are
//! determined by the value they decompose); here we confirm the backend solves
//! the bits correctly and that the reconstruction constraint does its job as a
//! range check.

use std::collections::HashMap;

use zkc_core::field::ZkField;
use zkc_core::goldilocks::Goldilocks;
use zkc_core::ir::Ir;
use zkc_core::witness::{solve, SolveInputs};

type F = Goldilocks;
fn g(v: u64) -> F {
    F::from_u64(v)
}

// low_bit(x) -> (b): returns bit 0 of x, decomposing x into 8 bits.
const LOWBIT_IR: &str = r#"{"schema_version":2,"name":"C","field":"bn254","const_one_wire":0,"inputs":[{"wire":1,"name":"x","visibility":"private","line":5},{"wire":2,"name":"b","visibility":"output","line":5}],"nodes":[{"wire":3,"advice_derived":true,"op":"hint","hint":"bits","bit":0,"name":"b0","gadget":"low_bit","line":2,"args":[1]},{"wire":4,"advice_derived":true,"op":"hint","hint":"bits","bit":1,"name":"b1","gadget":"low_bit","line":2,"args":[1]},{"wire":5,"advice_derived":true,"op":"hint","hint":"bits","bit":2,"name":"b2","gadget":"low_bit","line":2,"args":[1]},{"wire":6,"advice_derived":true,"op":"hint","hint":"bits","bit":3,"name":"b3","gadget":"low_bit","line":2,"args":[1]},{"wire":7,"advice_derived":true,"op":"hint","hint":"bits","bit":4,"name":"b4","gadget":"low_bit","line":2,"args":[1]},{"wire":8,"advice_derived":true,"op":"hint","hint":"bits","bit":5,"name":"b5","gadget":"low_bit","line":2,"args":[1]},{"wire":9,"advice_derived":true,"op":"hint","hint":"bits","bit":6,"name":"b6","gadget":"low_bit","line":2,"args":[1]},{"wire":10,"advice_derived":true,"op":"hint","hint":"bits","bit":7,"name":"b7","gadget":"low_bit","line":2,"args":[1]},{"wire":11,"advice_derived":false,"line":2,"op":"const","value":"1"},{"wire":12,"advice_derived":true,"line":2,"op":"sub","args":[11,3]},{"wire":13,"advice_derived":true,"line":2,"op":"mul","args":[3,12]},{"wire":14,"advice_derived":false,"line":2,"op":"const","value":"0"},{"wire":15,"advice_derived":true,"line":2,"op":"sub","args":[11,4]},{"wire":16,"advice_derived":true,"line":2,"op":"mul","args":[4,15]},{"wire":17,"advice_derived":true,"line":2,"op":"sub","args":[11,5]},{"wire":18,"advice_derived":true,"line":2,"op":"mul","args":[5,17]},{"wire":19,"advice_derived":true,"line":2,"op":"sub","args":[11,6]},{"wire":20,"advice_derived":true,"line":2,"op":"mul","args":[6,19]},{"wire":21,"advice_derived":true,"line":2,"op":"sub","args":[11,7]},{"wire":22,"advice_derived":true,"line":2,"op":"mul","args":[7,21]},{"wire":23,"advice_derived":true,"line":2,"op":"sub","args":[11,8]},{"wire":24,"advice_derived":true,"line":2,"op":"mul","args":[8,23]},{"wire":25,"advice_derived":true,"line":2,"op":"sub","args":[11,9]},{"wire":26,"advice_derived":true,"line":2,"op":"mul","args":[9,25]},{"wire":27,"advice_derived":true,"line":2,"op":"sub","args":[11,10]},{"wire":28,"advice_derived":true,"line":2,"op":"mul","args":[10,27]},{"wire":29,"advice_derived":true,"line":2,"op":"mul","args":[3,11]},{"wire":30,"advice_derived":false,"line":2,"op":"const","value":"2"},{"wire":31,"advice_derived":true,"line":2,"op":"mul","args":[4,30]},{"wire":32,"advice_derived":false,"line":2,"op":"const","value":"4"},{"wire":33,"advice_derived":true,"line":2,"op":"mul","args":[5,32]},{"wire":34,"advice_derived":false,"line":2,"op":"const","value":"8"},{"wire":35,"advice_derived":true,"line":2,"op":"mul","args":[6,34]},{"wire":36,"advice_derived":false,"line":2,"op":"const","value":"16"},{"wire":37,"advice_derived":true,"line":2,"op":"mul","args":[7,36]},{"wire":38,"advice_derived":false,"line":2,"op":"const","value":"32"},{"wire":39,"advice_derived":true,"line":2,"op":"mul","args":[8,38]},{"wire":40,"advice_derived":false,"line":2,"op":"const","value":"64"},{"wire":41,"advice_derived":true,"line":2,"op":"mul","args":[9,40]},{"wire":42,"advice_derived":false,"line":2,"op":"const","value":"128"},{"wire":43,"advice_derived":true,"line":2,"op":"mul","args":[10,42]},{"wire":44,"advice_derived":true,"line":2,"op":"add","args":[41,43]},{"wire":45,"advice_derived":true,"line":2,"op":"add","args":[39,44]},{"wire":46,"advice_derived":true,"line":2,"op":"add","args":[37,45]},{"wire":47,"advice_derived":true,"line":2,"op":"add","args":[35,46]},{"wire":48,"advice_derived":true,"line":2,"op":"add","args":[33,47]},{"wire":49,"advice_derived":true,"line":2,"op":"add","args":[31,48]},{"wire":50,"advice_derived":true,"line":2,"op":"add","args":[29,49]}],"assertions":[{"lhs":13,"rhs":14,"label":"(b0 * (1 - b0)) == 0","line":2},{"lhs":16,"rhs":14,"label":"(b1 * (1 - b1)) == 0","line":2},{"lhs":18,"rhs":14,"label":"(b2 * (1 - b2)) == 0","line":2},{"lhs":20,"rhs":14,"label":"(b3 * (1 - b3)) == 0","line":2},{"lhs":22,"rhs":14,"label":"(b4 * (1 - b4)) == 0","line":2},{"lhs":24,"rhs":14,"label":"(b5 * (1 - b5)) == 0","line":2},{"lhs":26,"rhs":14,"label":"(b6 * (1 - b6)) == 0","line":2},{"lhs":28,"rhs":14,"label":"(b7 * (1 - b7)) == 0","line":2},{"lhs":1,"rhs":50,"label":"x == ((b0 * 1) + ((b1 * 2) + ((b2 * 4) + ((b3 * 8) + ((b4 * 16) + ((b5 * 32) + ((b6 * 64) + (b7 * 128))))))))","line":2},{"lhs":2,"rhs":3,"label":"b == b0","line":3}],"determinacy":{"proved":true,"targets":["b"],"branches":[[]]}}"#;
// range8(x) -> (o): o == x, with x decomposed into 8 bits (so x in [0, 256)).
const RANGE8_IR: &str = r#"{"schema_version":2,"name":"T","field":"bn254","const_one_wire":0,"inputs":[{"wire":1,"name":"x","visibility":"private","line":2},{"wire":2,"name":"o","visibility":"output","line":2}],"nodes":[{"wire":3,"advice_derived":true,"op":"hint","hint":"bits","bit":0,"name":"b0","gadget":"range8","line":9,"args":[1]},{"wire":4,"advice_derived":true,"op":"hint","hint":"bits","bit":1,"name":"b1","gadget":"range8","line":9,"args":[1]},{"wire":5,"advice_derived":true,"op":"hint","hint":"bits","bit":2,"name":"b2","gadget":"range8","line":9,"args":[1]},{"wire":6,"advice_derived":true,"op":"hint","hint":"bits","bit":3,"name":"b3","gadget":"range8","line":9,"args":[1]},{"wire":7,"advice_derived":true,"op":"hint","hint":"bits","bit":4,"name":"b4","gadget":"range8","line":9,"args":[1]},{"wire":8,"advice_derived":true,"op":"hint","hint":"bits","bit":5,"name":"b5","gadget":"range8","line":9,"args":[1]},{"wire":9,"advice_derived":true,"op":"hint","hint":"bits","bit":6,"name":"b6","gadget":"range8","line":9,"args":[1]},{"wire":10,"advice_derived":true,"op":"hint","hint":"bits","bit":7,"name":"b7","gadget":"range8","line":9,"args":[1]},{"wire":11,"advice_derived":false,"line":9,"op":"const","value":"1"},{"wire":12,"advice_derived":true,"line":9,"op":"sub","args":[11,3]},{"wire":13,"advice_derived":true,"line":9,"op":"mul","args":[3,12]},{"wire":14,"advice_derived":false,"line":9,"op":"const","value":"0"},{"wire":15,"advice_derived":true,"line":9,"op":"sub","args":[11,4]},{"wire":16,"advice_derived":true,"line":9,"op":"mul","args":[4,15]},{"wire":17,"advice_derived":true,"line":9,"op":"sub","args":[11,5]},{"wire":18,"advice_derived":true,"line":9,"op":"mul","args":[5,17]},{"wire":19,"advice_derived":true,"line":9,"op":"sub","args":[11,6]},{"wire":20,"advice_derived":true,"line":9,"op":"mul","args":[6,19]},{"wire":21,"advice_derived":true,"line":9,"op":"sub","args":[11,7]},{"wire":22,"advice_derived":true,"line":9,"op":"mul","args":[7,21]},{"wire":23,"advice_derived":true,"line":9,"op":"sub","args":[11,8]},{"wire":24,"advice_derived":true,"line":9,"op":"mul","args":[8,23]},{"wire":25,"advice_derived":true,"line":9,"op":"sub","args":[11,9]},{"wire":26,"advice_derived":true,"line":9,"op":"mul","args":[9,25]},{"wire":27,"advice_derived":true,"line":9,"op":"sub","args":[11,10]},{"wire":28,"advice_derived":true,"line":9,"op":"mul","args":[10,27]},{"wire":29,"advice_derived":true,"line":9,"op":"mul","args":[3,11]},{"wire":30,"advice_derived":false,"line":9,"op":"const","value":"2"},{"wire":31,"advice_derived":true,"line":9,"op":"mul","args":[4,30]},{"wire":32,"advice_derived":false,"line":9,"op":"const","value":"4"},{"wire":33,"advice_derived":true,"line":9,"op":"mul","args":[5,32]},{"wire":34,"advice_derived":false,"line":9,"op":"const","value":"8"},{"wire":35,"advice_derived":true,"line":9,"op":"mul","args":[6,34]},{"wire":36,"advice_derived":false,"line":9,"op":"const","value":"16"},{"wire":37,"advice_derived":true,"line":9,"op":"mul","args":[7,36]},{"wire":38,"advice_derived":false,"line":9,"op":"const","value":"32"},{"wire":39,"advice_derived":true,"line":9,"op":"mul","args":[8,38]},{"wire":40,"advice_derived":false,"line":9,"op":"const","value":"64"},{"wire":41,"advice_derived":true,"line":9,"op":"mul","args":[9,40]},{"wire":42,"advice_derived":false,"line":9,"op":"const","value":"128"},{"wire":43,"advice_derived":true,"line":9,"op":"mul","args":[10,42]},{"wire":44,"advice_derived":true,"line":9,"op":"add","args":[41,43]},{"wire":45,"advice_derived":true,"line":9,"op":"add","args":[39,44]},{"wire":46,"advice_derived":true,"line":9,"op":"add","args":[37,45]},{"wire":47,"advice_derived":true,"line":9,"op":"add","args":[35,46]},{"wire":48,"advice_derived":true,"line":9,"op":"add","args":[33,47]},{"wire":49,"advice_derived":true,"line":9,"op":"add","args":[31,48]},{"wire":50,"advice_derived":true,"line":9,"op":"add","args":[29,49]}],"assertions":[{"lhs":13,"rhs":14,"label":"(b0 * (1 - b0)) == 0","line":9},{"lhs":16,"rhs":14,"label":"(b1 * (1 - b1)) == 0","line":9},{"lhs":18,"rhs":14,"label":"(b2 * (1 - b2)) == 0","line":9},{"lhs":20,"rhs":14,"label":"(b3 * (1 - b3)) == 0","line":9},{"lhs":22,"rhs":14,"label":"(b4 * (1 - b4)) == 0","line":9},{"lhs":24,"rhs":14,"label":"(b5 * (1 - b5)) == 0","line":9},{"lhs":26,"rhs":14,"label":"(b6 * (1 - b6)) == 0","line":9},{"lhs":28,"rhs":14,"label":"(b7 * (1 - b7)) == 0","line":9},{"lhs":1,"rhs":50,"label":"x == ((b0 * 1) + ((b1 * 2) + ((b2 * 4) + ((b3 * 8) + ((b4 * 16) + ((b5 * 32) + ((b6 * 64) + (b7 * 128))))))))","line":9},{"lhs":2,"rhs":1,"label":"out == x","line":10}],"determinacy":{"proved":true,"targets":["o"],"branches":[[]]}}"#;

fn solved(ir: &Ir, inputs: &[(&str, F)]) -> Vec<F> {
    let map: HashMap<String, F> =
        inputs.iter().map(|(k, v)| ((*k).to_string(), *v)).collect();
    solve::<F>(ir, &SolveInputs { inputs: &map, advice_overrides: &HashMap::new() }).unwrap()
}

#[test]
fn bits_solver_extracts_the_low_bits() {
    let ir = Ir::from_json(LOWBIT_IR).unwrap();
    // x = 0b1010_0101 = 165. Bit 0 is 1, bit 1 is 0, bit 2 is 1, ...
    let wires = solved(&ir, &[("x", g(165)), ("b", g(1))]);
    assert!(ir.is_satisfied::<F>(&wires), "honest witness satisfies");

    // The eight bit wires are wires 3..=10 (hints, low to high) in the compiled IR.
    let bits: Vec<u64> = (3..=10)
        .map(|w| wires[w].to_decimal().parse().unwrap())
        .collect();
    assert_eq!(bits, vec![1, 0, 1, 0, 0, 1, 0, 1], "bits are the low bits of 165");
}

#[test]
fn low_bit_output_is_bit_zero() {
    let ir = Ir::from_json(LOWBIT_IR).unwrap();
    // Even x -> low bit 0; odd x -> low bit 1.
    for x in [0u64, 1, 2, 3, 100, 101, 254, 255] {
        let b = x & 1;
        let wires = solved(&ir, &[("x", g(x)), ("b", g(b))]);
        assert!(ir.is_satisfied::<F>(&wires), "x={x} b={b} satisfies");
        // A wrong claimed low bit must NOT satisfy.
        let wrong = solved(&ir, &[("x", g(x)), ("b", g(1 - b))]);
        assert!(!ir.is_satisfied::<F>(&wrong), "x={x} wrong low bit rejected");
    }
}

#[test]
fn bits_reconstruction_is_a_range_check() {
    let ir = Ir::from_json(RANGE8_IR).unwrap();
    // In range [0, 256): reconstruction holds.
    for x in [0u64, 1, 100, 200, 255] {
        let wires = solved(&ir, &[("x", g(x)), ("o", g(x))]);
        assert!(ir.is_satisfied::<F>(&wires), "x={x} is in range and satisfies");
    }
    // Out of range: the solver produces the low 8 bits, whose weighted sum is
    // x mod 256 != x, so the reconstruction constraint fails. That is the range
    // check the language could not express before .
    for x in [256u64, 300, 1000, 65_537] {
        let wires = solved(&ir, &[("x", g(x)), ("o", g(x))]);
        assert!(!ir.is_satisfied::<F>(&wires), "x={x} is out of range and is rejected");
    }
}