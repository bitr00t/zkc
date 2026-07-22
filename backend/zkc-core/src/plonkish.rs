//! Plonkish arithmetization: rows, selectors, and copy constraints.
//!
//! This is the second lowering target, and its reason for existing is as much
//! architectural as practical. Invariant 1 says the Core IR is
//! arithmetization-agnostic — "a typed constraint graph, not an R1CS in
//! disguise" — but with only one lowering that claim was never tested. Nothing
//! would have gone wrong if the IR had quietly grown R1CS-shaped assumptions.
//! A second target from the same IR makes the claim falsifiable.
//!
//! ## The shape
//!
//! A Plonkish circuit is a table. Each row carries three **witness cells**
//! (columns `a`, `b`, `c`) and five **selector** constants, and must satisfy
//! one identity:
//!
//! ```text
//!     q_L·a  +  q_R·b  +  q_O·c  +  q_M·a·b  +  q_C  =  0
//! ```
//!
//! Setting the selectors chooses what the row *does*: `q_M = 1, q_O = -1`
//! makes it a multiplication; `q_L = q_R = 1, q_O = -1` an addition; and so
//! on. The gate is generic, and specialised per row.
//!
//! ## Why copy constraints exist
//!
//! Here is the part that has no R1CS counterpart, and the part worth
//! understanding. In R1CS a wire *is* a variable: referring to it twice is
//! free, because both references name the same index in one global assignment
//! vector. In Plonkish there is no global vector — there are only cells, and a
//! cell belongs to one row. A value produced in row 3 and consumed in row 7
//! occupies two unrelated cells, and nothing whatsoever forces them to agree.
//!
//! So the wiring has to be asserted. A **copy constraint** says "these two
//! cells hold the same value", and the set of them is what turns a table of
//! independent rows back into a connected circuit. In a real prover they are
//! enforced by a permutation argument over the columns; here they are an
//! explicit relation, checked directly (see `check`). Building the permutation
//! polynomial is the prover's job, and the prover is phase 5.
//!
//! This is exactly the kind of difference the neutral IR was supposed to
//! absorb: R1CS pays for sharing with nothing and for multiplication with a
//! constraint; Plonkish pays for sharing with a copy and gets a multiplication
//! and some linear terms in the same row. Same graph, different bills.
//!
//! ## What this module does *not* do
//!
//! Nothing here is optimised. Every node becomes its own row, which — as the
//! phase-4 design note predicts and measures — costs roughly twice what R1CS
//! does on our examples. Folding assertions and their operands into single
//! rows is the Plonkish-native optimisation, and it is deliberately separate
//! work, so that the fusion's win can be measured against this baseline the
//! way Workstream C's was.

use std::collections::HashMap;

use crate::field::ZkField;
use crate::ir::{Ir, NodeOp};

/// The three witness columns.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Column {
    A,
    B,
    C,
}

impl Column {
    pub fn index(self) -> usize {
        match self {
            Column::A => 0,
            Column::B => 1,
            Column::C => 2,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Column::A => "a",
            Column::B => "b",
            Column::C => "c",
        }
    }
}

/// One witness cell: a column at a row. The unit a copy constraint relates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Cell {
    pub row: usize,
    pub column: Column,
}

impl Cell {
    pub fn new(row: usize, column: Column) -> Self {
        Cell { row, column }
    }
}

/// A single row: the five selectors, plus which IR wire each cell holds.
///
/// A cell may be empty, in which case the selector multiplying it is zero and
/// its value is irrelevant. The lowering maintains that pairing; `check`
/// does not have to trust it, since an empty cell is simply assigned zero.
#[derive(Debug, Clone)]
pub struct Row<F> {
    pub q_l: F,
    pub q_r: F,
    pub q_o: F,
    pub q_m: F,
    pub q_c: F,
    /// Which IR wire occupies each cell, indexed by `Column::index`.
    pub cells: [Option<u32>; 3],
    /// Where this row came from, in the user's own words.
    pub origin: String,
}

impl<F: ZkField> Row<F> {
    fn empty(origin: String) -> Self {
        Row {
            q_l: F::zero(),
            q_r: F::zero(),
            q_o: F::zero(),
            q_m: F::zero(),
            q_c: F::zero(),
            cells: [None, None, None],
            origin,
        }
    }

    /// Evaluate the gate identity. Zero means satisfied.
    pub fn evaluate(&self, values: &[F; 3]) -> F {
        let (a, b, c) = (values[0], values[1], values[2]);
        self.q_l
            .mul(a)
            .add(self.q_r.mul(b))
            .add(self.q_o.mul(c))
            .add(self.q_m.mul(a).mul(b))
            .add(self.q_c)
    }
}

#[derive(Debug, Clone)]
pub struct Plonkish<F> {
    pub rows: Vec<Row<F>>,
    /// Cells that must agree. This is the wiring, made explicit.
    pub copies: Vec<(Cell, Cell)>,
    /// Public inputs, in declaration order: the wire and the cell that carries
    /// it. The ordering is part of the contract with the verifier.
    pub public_cells: Vec<(u32, Cell)>,
}

/// A failed check, in terms a circuit author can act on.
#[derive(Debug, Clone)]
pub enum Violation {
    /// A row's gate identity did not evaluate to zero.
    Gate {
        row: usize,
        origin: String,
        value: String,
    },
    /// Two cells that must agree did not. Either the lowering wired the
    /// circuit wrongly, or the assignment was tampered with after the fact.
    Copy {
        left: Cell,
        right: Cell,
        left_value: String,
        right_value: String,
    },
}

impl<F: ZkField> Plonkish<F> {
    pub fn num_rows(&self) -> usize {
        self.rows.len()
    }

    /// Three witness columns and five selector columns, always. Width is fixed
    /// by the gate; it is the row count that varies with the circuit.
    pub fn num_columns(&self) -> usize {
        8
    }

    /// Fill every cell from solved wire values — the honest prover's table.
    ///
    /// Copy constraints are satisfied by construction here, which is the
    /// point: they encode the wiring the *lowering* chose. `check` verifies
    /// them anyway, so that a table which did not come from this function
    /// (a tampered one, say) is still caught.
    pub fn assignment(&self, wire_values: &[F]) -> Vec<[F; 3]> {
        self.rows
            .iter()
            .map(|row| {
                let mut values = [F::zero(); 3];
                for (index, slot) in row.cells.iter().enumerate() {
                    if let Some(wire) = slot {
                        values[index] = wire_values[*wire as usize];
                    }
                }
                values
            })
            .collect()
    }

    fn cell_value(&self, assignment: &[[F; 3]], cell: Cell) -> F {
        assignment[cell.row][cell.column.index()]
    }

    pub fn check(&self, assignment: &[[F; 3]]) -> Vec<Violation> {
        let mut violations = Vec::new();

        for (index, row) in self.rows.iter().enumerate() {
            let value = row.evaluate(&assignment[index]);
            if !value.is_zero() {
                violations.push(Violation::Gate {
                    row: index,
                    origin: row.origin.clone(),
                    value: value.to_decimal(),
                });
            }
        }

        for (left, right) in &self.copies {
            let left_value = self.cell_value(assignment, *left);
            let right_value = self.cell_value(assignment, *right);
            if left_value != right_value {
                violations.push(Violation::Copy {
                    left: *left,
                    right: *right,
                    left_value: left_value.to_decimal(),
                    right_value: right_value.to_decimal(),
                });
            }
        }

        violations
    }

    pub fn is_satisfied(&self, assignment: &[[F; 3]]) -> bool {
        self.check(assignment).is_empty()
    }
}

/// Lower with gate fusion enabled (the default).
pub fn lower_plonkish<F: ZkField>(ir: &Ir) -> Result<Plonkish<F>, String> {
    lower_plonkish_with(ir, true)
}

/// Lower, optionally without fusion. `fuse = false` is the row-per-node
/// baseline the fusion is measured against — the same arrangement
/// `lower_with(ir, false)` provides on the R1CS side, and for the same reason:
/// a win nobody can reproduce as a delta is not a measurement.
pub fn lower_plonkish_with<F: ZkField>(ir: &Ir, fuse: bool) -> Result<Plonkish<F>, String> {
    if fuse {
        fuse::lower_fused(ir)
    } else {
        lower_unfused(ir)
    }
}

/// Lower the Core IR to a Plonkish circuit, one row per node.
///
/// One row per arithmetic node, one row per assertion, and no row at all for a
/// hint — a hint is an unconstrained value, so it occupies cells but imposes
/// no identity, exactly as it allocates a variable and no constraint in R1CS.
/// That symmetry is not a coincidence: "the prover chooses this freely" is a
/// property of the IR, and both arithmetizations have to express it.
fn lower_unfused<F: ZkField>(ir: &Ir) -> Result<Plonkish<F>, String> {
    let one = F::one();
    let minus_one = one.neg();
    let mut rows: Vec<Row<F>> = Vec::new();

    for node in &ir.nodes {
        match &node.op {
            // A hint imposes no identity: the prover picks the value. It gets
            // no row; it will occupy cells wherever it is used.
            NodeOp::Hint { .. } => continue,

            NodeOp::Const { value } => {
                // c = value, i.e. c - value = 0.
                let mut row = Row::empty(format!("const at wire {}", node.wire));
                row.q_o = one;
                row.q_c = F::from_decimal(value)?.neg();
                row.cells[Column::C.index()] = Some(node.wire);
                rows.push(row);
            }

            NodeOp::Add { args } => {
                let mut row = Row::empty(format!("add at wire {}", node.wire));
                row.q_l = one;
                row.q_r = one;
                row.q_o = minus_one;
                row.cells = [Some(args[0]), Some(args[1]), Some(node.wire)];
                rows.push(row);
            }

            NodeOp::Sub { args } => {
                let mut row = Row::empty(format!("sub at wire {}", node.wire));
                row.q_l = one;
                row.q_r = minus_one;
                row.q_o = minus_one;
                row.cells = [Some(args[0]), Some(args[1]), Some(node.wire)];
                rows.push(row);
            }

            NodeOp::Mul { args } => {
                let mut row = Row::empty(format!("mul at wire {}", node.wire));
                row.q_m = one;
                row.q_o = minus_one;
                row.cells = [Some(args[0]), Some(args[1]), Some(node.wire)];
                rows.push(row);
            }

            NodeOp::Neg { args } => {
                let mut row = Row::empty(format!("neg at wire {}", node.wire));
                row.q_l = minus_one;
                row.q_o = minus_one;
                row.cells = [Some(args[0]), None, Some(node.wire)];
                rows.push(row);
            }
        }
    }

    for assertion in &ir.assertions {
        // lhs - rhs = 0. The `c` cell stays empty, and q_O is zero with it.
        let mut row = Row::empty(format!("line {}: {}", assertion.line, assertion.label));
        row.q_l = one;
        row.q_r = minus_one;
        row.cells = [Some(assertion.lhs), Some(assertion.rhs), None];
        rows.push(row);
    }

    Ok(finish(rows, ir))
}

/// Shared post-processing: derive the wiring from where wires actually landed.
///
/// Both lowerings place wires in cells and then owe the same two things: a
/// copy constraint wherever a wire occupies more than one cell, and a cell for
/// every public input. Deriving them from the finished rows rather than
/// tracking them during lowering means the two paths cannot disagree about the
/// wiring, which is one fewer way for the fused version to be subtly wrong.
fn finish<F: ZkField>(mut rows: Vec<Row<F>>, ir: &Ir) -> Plonkish<F> {
    let mut wire_cells: HashMap<u32, Vec<Cell>> = HashMap::new();
    let mut record = |rows: &Vec<Row<F>>, cells: &mut HashMap<u32, Vec<Cell>>| {
        cells.clear();
        for (index, row) in rows.iter().enumerate() {
            for (slot, wire) in row.cells.iter().enumerate() {
                if let Some(wire) = wire {
                    let column = match slot {
                        0 => Column::A,
                        1 => Column::B,
                        _ => Column::C,
                    };
                    cells.entry(*wire).or_default().push(Cell::new(index, column));
                }
            }
        }
    };
    record(&rows, &mut wire_cells);

    // A public input that no gate happens to mention still has to be bound to
    // a cell, or the verifier has nothing to point at. An all-zero row is
    // satisfied by any value, which is precisely what an unused input is.
    let unbound: Vec<_> = ir
        .inputs
        .iter()
        .filter(|input| input.visibility.is_public() && !wire_cells.contains_key(&input.wire))
        .map(|input| (input.wire, input.name.clone()))
        .collect();
    if !unbound.is_empty() {
        for (wire, name) in unbound {
            let mut row = Row::empty(format!("binding for public input '{name}'"));
            row.cells[Column::A.index()] = Some(wire);
            rows.push(row);
        }
        record(&rows, &mut wire_cells);
    }

    // Assert the wiring: every cell holding a given wire must agree with the
    // next. Chaining is enough — equality is transitive, and a chain costs
    // n-1 copies where relating every pair would cost n²/2.
    let mut copies: Vec<(Cell, Cell)> = Vec::new();
    let mut wires: Vec<u32> = wire_cells.keys().copied().collect();
    wires.sort();
    for wire in &wires {
        for pair in wire_cells[wire].windows(2) {
            copies.push((pair[0], pair[1]));
        }
    }

    let public_cells = ir
        .inputs
        .iter()
        .filter(|input| input.visibility.is_public())
        .map(|input| (input.wire, wire_cells[&input.wire][0]))
        .collect();

    Plonkish { rows, copies, public_cells }
}

/// Gate fusion — the Plonkish-native constraint-count optimisation.
///
/// Workstream C fused on the R1CS side because a rank-1 constraint has a spare
/// *product* slot: `assert a * b == c` fits in one constraint instead of two.
/// The opportunity here is the mirror image. A Plonkish row has spare *linear*
/// slots and a constant, but only three cells to spend, so the question is not
/// "is there a multiplication to absorb" but "does the whole expression still
/// fit in three cells".
///
/// So the rule is a budget, not a pattern. A node is folded into its consumer
/// while the resulting expression stays inside the cell budget; when it would
/// overflow, the node is *materialised* — given its own row and a cell of its
/// own — and the consumer refers to it by wire instead. Materialising is
/// always available and always fits, which is what makes the procedure total:
/// materialise everything and you are back at the unfused baseline.
///
/// Worked example, `assert x * inv == 1 - out`. Unfused that is four rows: a
/// constant, a subtraction, a multiplication, and the assertion. Fused, the
/// whole thing is one identity over three cells:
///
/// ```text
///     q_M·x·inv  +  q_O·out  +  q_C  =  0        with q_M = 1, q_O = 1, q_C = -1
/// ```
///
/// Values shared by more than one consumer are materialised up front, for the
/// same reason common-subexpression elimination exists: inlining them twice
/// would recompute them in two gates rather than wire one result to both.
mod fuse {
    use super::*;
    use crate::ir::Node;
    use std::collections::HashSet;
    use std::marker::PhantomData;

    /// Everything a single gate can hold: a linear combination, at most one
    /// product, and a constant.
    #[derive(Clone, Debug)]
    pub(super) struct Expr<F> {
        linear: Vec<(u32, F)>,
        product: Option<(u32, u32, F)>,
        constant: F,
    }

    impl<F: ZkField> Expr<F> {
        fn constant(value: F) -> Self {
            Expr { linear: Vec::new(), product: None, constant: value }
        }

        fn wire(wire: u32) -> Self {
            Expr { linear: vec![(wire, F::one())], product: None, constant: F::zero() }
        }

        fn is_bare_wire(&self) -> bool {
            self.product.is_none() && self.constant.is_zero() && self.linear.len() == 1
        }

        fn coeff_of(&self, wire: u32) -> F {
            self.linear
                .iter()
                .find(|(w, _)| *w == wire)
                .map(|(_, c)| *c)
                .unwrap_or_else(F::zero)
        }

        fn add_linear(&mut self, wire: u32, coeff: F) {
            if coeff.is_zero() {
                return;
            }
            match self.linear.iter_mut().find(|(w, _)| *w == wire) {
                Some((_, existing)) => *existing = existing.add(coeff),
                None => self.linear.push((wire, coeff)),
            }
            self.linear.retain(|(_, c)| !c.is_zero());
        }

        fn scale(&self, factor: F) -> Self {
            Expr {
                linear: self
                    .linear
                    .iter()
                    .map(|(w, c)| (*w, c.mul(factor)))
                    .filter(|(_, c)| !c.is_zero())
                    .collect(),
                product: self.product.map(|(a, b, m)| (a, b, m.mul(factor))),
                constant: self.constant.mul(factor),
            }
        }

        /// Sum. Fails when both sides carry a product a single gate cannot
        /// hold two of — unless they happen to be the same product, which can
        /// simply have its coefficients added.
        fn add(&self, other: &Self) -> Option<Self> {
            let product = match (self.product, other.product) {
                (None, p) | (p, None) => p,
                (Some((a1, b1, m1)), Some((a2, b2, m2))) => {
                    let same = (a1 == a2 && b1 == b2) || (a1 == b2 && b1 == a2);
                    if same {
                        let merged = m1.add(m2);
                        if merged.is_zero() { None } else { Some((a1, b1, merged)) }
                    } else {
                        return None;
                    }
                }
            };
            let mut result = Expr {
                linear: self.linear.clone(),
                product,
                constant: self.constant.add(other.constant),
            };
            for (wire, coeff) in &other.linear {
                result.add_linear(*wire, *coeff);
            }
            Some(result)
        }

        fn sub(&self, other: &Self) -> Option<Self> {
            self.add(&other.scale(F::one().neg()))
        }

        /// Product. A gate holds one multiplication of two cells, so this
        /// succeeds when each side is affine in at most one wire: the cross
        /// terms then land in the gate's linear slots. `(a + 1) * b` becomes
        /// `a·b + b`, which is one gate; `(a + b) * (c + d)` is not, and the
        /// caller responds by materialising a side.
        fn try_mul(&self, other: &Self) -> Option<Self> {
            if self.product.is_some() || other.product.is_some() {
                return None;
            }
            if self.linear.is_empty() {
                return Some(other.scale(self.constant));
            }
            if other.linear.is_empty() {
                return Some(self.scale(other.constant));
            }
            if self.linear.len() > 1 || other.linear.len() > 1 {
                return None;
            }
            let (w1, c1) = self.linear[0];
            let (w2, c2) = other.linear[0];
            let mut result = Expr {
                linear: Vec::new(),
                product: Some((w1, w2, c1.mul(c2))),
                constant: self.constant.mul(other.constant),
            };
            result.add_linear(w1, c1.mul(other.constant));
            result.add_linear(w2, c2.mul(self.constant));
            Some(result)
        }

        /// How many witness cells this expression needs. The product occupies
        /// cells `a` and `b` — two of them even when both factors are the same
        /// wire, since a cell holds one value — and anything else competes for
        /// the single remaining cell.
        fn cells(&self) -> usize {
            match self.product {
                Some((w1, w2, _)) => {
                    2 + self
                        .linear
                        .iter()
                        .filter(|(w, _)| *w != w1 && *w != w2)
                        .count()
                }
                None => self.linear.len(),
            }
        }

        /// Lay the expression out as a row. Assumes it fits.
        fn to_row(&self, origin: String) -> Row<F> {
            let mut row = Row::empty(origin);
            row.q_c = self.constant;
            match self.product {
                Some((w1, w2, m)) => {
                    row.q_m = m;
                    row.cells[Column::A.index()] = Some(w1);
                    row.cells[Column::B.index()] = Some(w2);
                    row.q_l = self.coeff_of(w1);
                    // Both cells hold the same value, so one selector carries
                    // the whole linear coefficient and the other stays zero.
                    row.q_r = if w1 == w2 { F::zero() } else { self.coeff_of(w2) };
                    if let Some((wire, coeff)) =
                        self.linear.iter().find(|(w, _)| *w != w1 && *w != w2)
                    {
                        row.cells[Column::C.index()] = Some(*wire);
                        row.q_o = *coeff;
                    }
                }
                None => {
                    for (slot, (wire, coeff)) in self.linear.iter().enumerate() {
                        row.cells[slot] = Some(*wire);
                        match slot {
                            0 => row.q_l = *coeff,
                            1 => row.q_r = *coeff,
                            _ => row.q_o = *coeff,
                        }
                    }
                }
            }
            row
        }
    }

    #[derive(Clone, Copy)]
    enum Op {
        Add,
        Sub,
        Mul,
    }

    fn apply<F: ZkField>(op: Op, left: &Expr<F>, right: &Expr<F>) -> Option<Expr<F>> {
        match op {
            Op::Add => left.add(right),
            Op::Sub => left.sub(right),
            Op::Mul => left.try_mul(right),
        }
    }

    struct Fuser<'a, F> {
        ir: &'a Ir,
        nodes: HashMap<u32, &'a Node>,
        /// Nodes that must get a row and a cell of their own.
        materialised: HashSet<u32>,
        marker: PhantomData<F>,
    }

    impl<'a, F: ZkField> Fuser<'a, F> {
        fn new(ir: &'a Ir) -> Self {
            let nodes: HashMap<u32, &Node> = ir.nodes.iter().map(|n| (n.wire, n)).collect();

            // Seed with values used more than once. Inlining those would
            // recompute them in every consumer instead of wiring one result to
            // all of them — the same reasoning as common-subexpression
            // elimination, one arithmetization further down.
            let mut uses: HashMap<u32, usize> = HashMap::new();
            for node in &ir.nodes {
                for arg in node.op.args() {
                    *uses.entry(*arg).or_insert(0) += 1;
                }
            }
            for assertion in &ir.assertions {
                *uses.entry(assertion.lhs).or_insert(0) += 1;
                *uses.entry(assertion.rhs).or_insert(0) += 1;
            }
            let materialised = nodes
                .keys()
                .copied()
                .filter(|wire| uses.get(wire).copied().unwrap_or(0) > 1)
                .collect();

            Fuser { ir, nodes, materialised, marker: PhantomData }
        }

        /// An atom is a value no gate defines: an input, or a hint the prover
        /// chooses. It always lives in a cell.
        fn is_atom(&self, wire: u32) -> bool {
            match self.nodes.get(&wire) {
                None => true,
                Some(node) => matches!(node.op, NodeOp::Hint { .. }),
            }
        }

        /// The expression for a wire's value, folded into at most `budget`
        /// cells. Overflowing means the node earns its own row.
        fn build(&mut self, wire: u32, budget: usize) -> Result<Expr<F>, String> {
            if self.is_atom(wire) || self.materialised.contains(&wire) {
                return Ok(Expr::wire(wire));
            }
            let node = *self.nodes.get(&wire).expect("wire is a node");
            let expr = match &node.op {
                NodeOp::Hint { .. } => unreachable!("hints are atoms"),
                NodeOp::Const { value } => Expr::constant(F::from_decimal(value)?),
                NodeOp::Add { args } => self.binary(args[0], args[1], Op::Add, budget)?,
                NodeOp::Sub { args } => self.binary(args[0], args[1], Op::Sub, budget)?,
                NodeOp::Mul { args } => self.binary(args[0], args[1], Op::Mul, budget)?,
                NodeOp::Neg { args } => {
                    let inner = self.build(args[0], budget)?;
                    inner.scale(F::one().neg())
                }
            };
            if expr.cells() <= budget {
                Ok(expr)
            } else {
                self.materialised.insert(wire);
                Ok(Expr::wire(wire))
            }
        }

        fn binary(&mut self, x: u32, y: u32, op: Op, budget: usize) -> Result<Expr<F>, String> {
            let left = self.build(x, budget)?;
            // Spend what is left on the second operand, rather than letting it
            // expand and then throwing the work away.
            let remaining = budget.saturating_sub(left.cells());
            let right = self.build(y, remaining)?;
            self.combine(x, y, left, right, op, budget)
        }

        /// Combine two operands, materialising whichever side is costing the
        /// most until the result fits. Two bare wires always fit, so this
        /// terminates.
        fn combine(
            &mut self,
            x: u32,
            y: u32,
            mut left: Expr<F>,
            mut right: Expr<F>,
            op: Op,
            budget: usize,
        ) -> Result<Expr<F>, String> {
            loop {
                if let Some(combined) = apply(op, &left, &right) {
                    if combined.cells() <= budget {
                        return Ok(combined);
                    }
                }
                let left_reducible = !left.is_bare_wire() && !self.is_atom(x);
                let right_reducible = !right.is_bare_wire() && !self.is_atom(y);
                if left_reducible && (left.cells() >= right.cells() || !right_reducible) {
                    self.materialised.insert(x);
                    left = Expr::wire(x);
                } else if right_reducible {
                    self.materialised.insert(y);
                    right = Expr::wire(y);
                } else {
                    // Nothing left to give: both operands are single cells, so
                    // the combination is as small as it can be.
                    return apply(op, &left, &right).ok_or_else(|| {
                        format!("cannot express wires {x} and {y} in one gate")
                    });
                }
            }
        }

        /// The gate defining a materialised node: `definition - wire = 0`.
        /// The definition gets two cells; the third holds the wire itself.
        fn node_gate(&mut self, wire: u32) -> Result<Expr<F>, String> {
            let node = *self.nodes.get(&wire).expect("materialised wire is a node");
            let definition = match &node.op {
                NodeOp::Hint { .. } => unreachable!("hints impose no identity"),
                NodeOp::Const { value } => Expr::constant(F::from_decimal(value)?),
                NodeOp::Add { args } => self.binary(args[0], args[1], Op::Add, 2)?,
                NodeOp::Sub { args } => self.binary(args[0], args[1], Op::Sub, 2)?,
                NodeOp::Mul { args } => self.binary(args[0], args[1], Op::Mul, 2)?,
                NodeOp::Neg { args } => {
                    let inner = self.build(args[0], 2)?;
                    inner.scale(F::one().neg())
                }
            };
            definition
                .sub(&Expr::wire(wire))
                .ok_or_else(|| format!("cannot express the definition of wire {wire} in one gate"))
        }
    }

    pub(super) fn lower_fused<F: ZkField>(ir: &Ir) -> Result<Plonkish<F>, String> {
        let mut fuser: Fuser<F> = Fuser::new(ir);

        // Assertions first: they are what the circuit is *for*, and folding
        // them is what decides which intermediate values survive.
        let mut assertion_rows = Vec::new();
        for assertion in &ir.assertions {
            let left = fuser.build(assertion.lhs, 3)?;
            let remaining = 3usize.saturating_sub(left.cells());
            let right = fuser.build(assertion.rhs, remaining)?;
            let expr =
                fuser.combine(assertion.lhs, assertion.rhs, left, right, Op::Sub, 3)?;
            assertion_rows
                .push(expr.to_row(format!("line {}: {}", assertion.line, assertion.label)));
        }

        // Then a row for everything that had to be materialised — including
        // whatever the previous step materialised, and whatever *those* rows
        // materialise in turn.
        let mut node_rows: Vec<(u32, Row<F>)> = Vec::new();
        let mut emitted: HashSet<u32> = HashSet::new();
        loop {
            let pending: Vec<u32> = fuser
                .materialised
                .iter()
                .copied()
                .filter(|wire| !emitted.contains(wire) && !fuser.is_atom(*wire))
                .collect();
            if pending.is_empty() {
                break;
            }
            for wire in pending {
                emitted.insert(wire);
                let expr = fuser.node_gate(wire)?;
                node_rows.push((wire, expr.to_row(format!("wire {wire}"))));
            }
        }

        // Node rows before assertion rows, in wire order, matching the R1CS
        // lowering's arrangement so the two are read side by side.
        node_rows.sort_by_key(|(wire, _)| *wire);
        let mut rows: Vec<Row<F>> = node_rows.into_iter().map(|(_, row)| row).collect();
        rows.extend(assertion_rows);

        Ok(finish(rows, fuser.ir))
    }
}