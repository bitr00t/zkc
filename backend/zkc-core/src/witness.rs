//! The witness solver: the "compute" half of the compute/constrain split.
//!
//! Given values for the circuit inputs, this evaluates every node in
//! topological order and produces a value for every wire. Crucially, it
//! *only computes* — it has no idea whether the constraints will accept the
//! result. That separation is the entire subject of this compiler.
//!
//! Advice overrides model a dishonest prover. Hints exist precisely because
//! some values cannot be derived inside the constraint system, so the prover
//! supplies them; nothing stops the prover from supplying something else.
//! Being able to say so explicitly (`--advice inv=0`) is what lets the demo
//! reproduce a real forgery instead of just describing one.

use std::collections::HashMap;

use crate::field::ZkField;
use crate::ir::{HintKind, Ir, NodeOp};

pub struct SolveInputs<'a, F> {
    /// Value for every declared input, by name.
    pub inputs: &'a HashMap<String, F>,
    /// Optional replacements for hint-produced wires, by advice name.
    pub advice_overrides: &'a HashMap<String, F>,
}

/// Evaluate all wires. Index `i` of the result is the value of wire `i`.
pub fn solve<F: ZkField>(ir: &Ir, args: &SolveInputs<F>) -> Result<Vec<F>, String> {
    let mut values = vec![F::zero(); ir.wire_count()];
    values[ir.const_one_wire as usize] = F::one();

    for input in &ir.inputs {
        let value = args
            .inputs
            .get(&input.name)
            .copied()
            .ok_or_else(|| format!("no value supplied for input '{}'", input.name))?;
        values[input.wire as usize] = value;
    }

    for node in &ir.nodes {
        let arg = |index: usize| values[node.op.args()[index] as usize];
        let value = match &node.op {
            NodeOp::Const { value } => F::from_decimal(value)?,
            NodeOp::Add { .. } => arg(0).add(arg(1)),
            NodeOp::Sub { .. } => arg(0).sub(arg(1)),
            NodeOp::Mul { .. } => arg(0).mul(arg(1)),
            NodeOp::Neg { .. } => arg(0).neg(),
            NodeOp::Hint { hint, name, .. } => match args.advice_overrides.get(name) {
                // A dishonest prover simply ignores the hint.
                Some(override_value) => *override_value,
                None => match hint {
                    HintKind::InvOrZero => arg(0).inverse().unwrap_or_else(F::zero),
                    HintKind::Inv => arg(0).inverse().ok_or_else(|| {
                        format!("hint inv('{name}') is undefined: the argument is zero")
                    })?,
                },
            },
        };
        values[node.wire as usize] = value;
    }
    Ok(values)
}