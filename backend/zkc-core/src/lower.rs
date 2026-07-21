//! Lowering: Core IR to R1CS.
//!
//! This is where the arithmetization is chosen, and it shows why the IR must
//! not *be* R1CS. Each IR wire is mapped to a **linear combination** over
//! R1CS variables, and only operations that genuinely need a multiplication
//! allocate a variable and emit a constraint:
//!
//! | IR node          | cost in R1CS                                    |
//! |------------------|-------------------------------------------------|
//! | `const`          | free — a constant term on variable 0            |
//! | `add`/`sub`/`neg`| free — linear combinations fold together        |
//! | `mul`            | 1 new variable + 1 constraint                   |
//! | `hint`           | 1 new variable, **no constraint** (!)           |
//! | `assert l == r`  | 1 constraint: `(l - r) * 1 = 0`                 |
//!
//! Two things are worth staring at. First, linear algebra is free here but
//! would cost trace columns in an AIR backend — the same IR, a different
//! bill, which is exactly why the IR stays neutral. Second, a `hint`
//! allocates a variable with no constraint attached: that is
//! under-constraining rendered as compiler output, and precisely what the
//! phase-2 determinacy pass must prove is subsequently pinned down.

use crate::field::ZkField;
use crate::ir::{Ir, NodeOp};
use crate::r1cs::{Constraint, Lc, R1cs};

pub fn lower<F: ZkField>(ir: &Ir) -> Result<R1cs<F>, String> {
    let mut lcs: Vec<Lc<F>> = vec![Lc::zero(); ir.wire_count()];
    let mut constraints: Vec<Constraint<F>> = Vec::new();
    let mut public_vars: Vec<usize> = Vec::new();
    // Variable 0 is the constant one and holds no wire.
    let mut var_to_wire: Vec<Option<u32>> = vec![None];

    lcs[ir.const_one_wire as usize] = Lc::constant(F::one());

    for input in &ir.inputs {
        let var = var_to_wire.len();
        var_to_wire.push(Some(input.wire));
        if input.visibility.is_public() {
            public_vars.push(var);
        }
        lcs[input.wire as usize] = Lc::var(var);
    }

    for node in &ir.nodes {
        let arg = |index: usize, lcs: &Vec<Lc<F>>| lcs[node.op.args()[index] as usize].clone();
        let lc = match &node.op {
            NodeOp::Const { value } => Lc::constant(F::from_decimal(value)?),
            NodeOp::Add { .. } => arg(0, &lcs).add(&arg(1, &lcs)),
            NodeOp::Sub { .. } => arg(0, &lcs).sub(&arg(1, &lcs)),
            NodeOp::Neg { .. } => arg(0, &lcs).scale(F::one().neg()),
            NodeOp::Mul { .. } => {
                // The only IR node that inherently costs a constraint.
                let var = var_to_wire.len();
                var_to_wire.push(Some(node.wire));
                constraints.push(Constraint {
                    a: arg(0, &lcs),
                    b: arg(1, &lcs),
                    c: Lc::var(var),
                    origin: format!("multiplication at wire {}", node.wire),
                });
                Lc::var(var)
            }
            NodeOp::Hint { name, .. } => {
                // A free variable: the prover picks it. No constraint here —
                // that is the whole point, and the whole danger.
                let var = var_to_wire.len();
                var_to_wire.push(Some(node.wire));
                let _ = name;
                Lc::var(var)
            }
        };
        lcs[node.wire as usize] = lc;
    }

    for assertion in &ir.assertions {
        let difference = lcs[assertion.lhs as usize].sub(&lcs[assertion.rhs as usize]);
        constraints.push(Constraint {
            a: difference,
            b: Lc::constant(F::one()),
            c: Lc::zero(),
            origin: format!("line {}: {}", assertion.line, assertion.label),
        });
    }

    Ok(R1cs {
        num_vars: var_to_wire.len(),
        constraints,
        public_vars,
        var_to_wire,
    })
}