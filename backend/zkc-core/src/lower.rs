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
//!
//! ## Multiplicative-assertion fusion (phase 3, Workstream C)
//!
//! The single most common shape in a real circuit is `assert a * b == c`.
//! Lowered naively it costs **two** rank-1 constraints — `a * b = v` for the
//! `mul`, then `(v - c) * 1 = 0` for the assertion — for something R1CS
//! expresses natively in **one**: `a * b = c`. When a `mul` wire feeds
//! exactly one assertion and nothing else, its intermediate variable is
//! pure overhead: we skip it and emit the fused constraint directly. On
//! multiplication-heavy circuits (hashes are almost all field mults) this
//! roughly halves the constraint count.
//!
//! This lives *here*, in the lowering, and not in the neutral IR passes: that
//! `a * b == c` collapses to one rank-1 constraint is an R1CS fact. A future
//! AIR backend packs gates differently from the same IR — which is the whole
//! point of keeping the IR arithmetization-agnostic.

use std::collections::HashMap;

use crate::field::ZkField;
use crate::ir::{Ir, NodeOp};
use crate::r1cs::{Constraint, Lc, R1cs};

/// Lower with multiplicative-assertion fusion enabled (the default).
pub fn lower<F: ZkField>(ir: &Ir) -> Result<R1cs<F>, String> {
    lower_with(ir, true)
}

/// Lower, optionally without fusion. `fuse = false` reproduces the phase-2
/// lowering exactly, which is what the benchmark harness measures against and
/// what pins the fusion win to a number rather than an assertion.
pub fn lower_with<F: ZkField>(ir: &Ir, fuse: bool) -> Result<R1cs<F>, String> {
    let fused: FusedMuls = if fuse { find_fusible(ir) } else { FusedMuls::none() };

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
            NodeOp::Mul { .. } if fused.contains(node.wire) => {
                // Fused: this mul feeds exactly one assertion and nothing
                // else, so its variable would only ever be equated away. The
                // assertion below emits `a * b = other_side` in its place.
                // The wire's LC is never read (nothing else references it).
                Lc::zero()
            }
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

    for (index, assertion) in ir.assertions.iter().enumerate() {
        match fused.side_for(index) {
            // One side is a fused mul: emit `a * b = other_side` directly.
            Some((mul_wire, other_wire)) => {
                let (arg0, arg1) = fused.args(mul_wire);
                constraints.push(Constraint {
                    a: lcs[arg0 as usize].clone(),
                    b: lcs[arg1 as usize].clone(),
                    c: lcs[other_wire as usize].clone(),
                    origin: format!("line {}: {}", assertion.line, assertion.label),
                });
            }
            // No fusion: the honest `(l - r) * 1 = 0`.
            None => {
                let difference = lcs[assertion.lhs as usize].sub(&lcs[assertion.rhs as usize]);
                constraints.push(Constraint {
                    a: difference,
                    b: Lc::constant(F::one()),
                    c: Lc::zero(),
                    origin: format!("line {}: {}", assertion.line, assertion.label),
                });
            }
        }
    }

    Ok(R1cs {
        num_vars: var_to_wire.len(),
        constraints,
        public_vars,
        var_to_wire,
    })
}

/// The result of the fusibility analysis: which mul wires are fused, the two
/// arguments of each, and, per assertion, which side (if any) was fused.
struct FusedMuls {
    /// mul wire -> its two argument wires.
    args: HashMap<u32, (u32, u32)>,
    /// assertion index -> (fused mul wire, the other side's wire).
    per_assertion: HashMap<usize, (u32, u32)>,
}

impl FusedMuls {
    fn none() -> Self {
        FusedMuls { args: HashMap::new(), per_assertion: HashMap::new() }
    }
    fn contains(&self, wire: u32) -> bool {
        self.args.contains_key(&wire)
    }
    fn args(&self, wire: u32) -> (u32, u32) {
        self.args[&wire]
    }
    fn side_for(&self, assertion_index: usize) -> Option<(u32, u32)> {
        self.per_assertion.get(&assertion_index).copied()
    }
}

/// A mul wire is fusible when it is referenced by **exactly one** assertion
/// side and by **no** node — then its intermediate variable is redundant.
///
/// If an assertion has a fusible mul on *both* sides we can only fuse one
/// (a rank-1 constraint has a single product), so the other keeps its
/// variable and constraint. That is why the fused set is decided per
/// assertion, not per mul in isolation.
fn find_fusible(ir: &Ir) -> FusedMuls {
    // Argument lists of every mul, by wire.
    let mut mul_args: HashMap<u32, (u32, u32)> = HashMap::new();
    for node in &ir.nodes {
        if let NodeOp::Mul { args } = &node.op {
            mul_args.insert(node.wire, (args[0], args[1]));
        }
    }

    // How often each wire is used as a node argument, and across all
    // assertion sides.
    let mut node_uses: HashMap<u32, u32> = HashMap::new();
    for node in &ir.nodes {
        for &arg in node.op.args() {
            *node_uses.entry(arg).or_insert(0) += 1;
        }
    }
    let mut assert_uses: HashMap<u32, u32> = HashMap::new();
    for assertion in &ir.assertions {
        *assert_uses.entry(assertion.lhs).or_insert(0) += 1;
        *assert_uses.entry(assertion.rhs).or_insert(0) += 1;
    }

    let is_fusible = |wire: u32| {
        mul_args.contains_key(&wire)
            && *node_uses.get(&wire).unwrap_or(&0) == 0
            && *assert_uses.get(&wire).unwrap_or(&0) == 1
    };

    let mut per_assertion: HashMap<usize, (u32, u32)> = HashMap::new();
    let mut fused_args: HashMap<u32, (u32, u32)> = HashMap::new();
    for (index, assertion) in ir.assertions.iter().enumerate() {
        let (lhs, rhs) = (assertion.lhs, assertion.rhs);
        // Prefer the left side; fall back to the right. Never fuse when both
        // sides are the same wire.
        if lhs != rhs && is_fusible(lhs) {
            per_assertion.insert(index, (lhs, rhs));
            fused_args.insert(lhs, mul_args[&lhs]);
        } else if lhs != rhs && is_fusible(rhs) {
            per_assertion.insert(index, (rhs, lhs));
            fused_args.insert(rhs, mul_args[&rhs]);
        }
    }

    FusedMuls { args: fused_args, per_assertion }
}