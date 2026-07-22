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

/// Lower the Core IR to a Plonkish circuit.
///
/// One row per arithmetic node, one row per assertion, and no row at all for a
/// hint — a hint is an unconstrained value, so it occupies cells but imposes
/// no identity, exactly as it allocates a variable and no constraint in R1CS.
/// That symmetry is not a coincidence: "the prover chooses this freely" is a
/// property of the IR, and both arithmetizations have to express it.
pub fn lower_plonkish<F: ZkField>(ir: &Ir) -> Result<Plonkish<F>, String> {
    let mut rows: Vec<Row<F>> = Vec::new();
    // Every cell each wire occupies, so the wiring can be asserted afterwards.
    let mut wire_cells: HashMap<u32, Vec<Cell>> = HashMap::new();

    let place = |wire_cells: &mut HashMap<u32, Vec<Cell>>, row: usize, column: Column, wire: u32| {
        wire_cells.entry(wire).or_default().push(Cell::new(row, column));
    };

    let one = F::one();
    let minus_one = one.neg();

    for node in &ir.nodes {
        let index = rows.len();
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
                place(&mut wire_cells, index, Column::C, node.wire);
            }

            NodeOp::Add { args } => {
                // a + b - c = 0
                let mut row = Row::empty(format!("add at wire {}", node.wire));
                row.q_l = one;
                row.q_r = one;
                row.q_o = minus_one;
                row.cells = [Some(args[0]), Some(args[1]), Some(node.wire)];
                rows.push(row);
                place(&mut wire_cells, index, Column::A, args[0]);
                place(&mut wire_cells, index, Column::B, args[1]);
                place(&mut wire_cells, index, Column::C, node.wire);
            }

            NodeOp::Sub { args } => {
                // a - b - c = 0
                let mut row = Row::empty(format!("sub at wire {}", node.wire));
                row.q_l = one;
                row.q_r = minus_one;
                row.q_o = minus_one;
                row.cells = [Some(args[0]), Some(args[1]), Some(node.wire)];
                rows.push(row);
                place(&mut wire_cells, index, Column::A, args[0]);
                place(&mut wire_cells, index, Column::B, args[1]);
                place(&mut wire_cells, index, Column::C, node.wire);
            }

            NodeOp::Mul { args } => {
                // a·b - c = 0 — the one place R1CS also has to spend a
                // constraint, though here it shares the row with whatever
                // linear terms the gate has spare.
                let mut row = Row::empty(format!("mul at wire {}", node.wire));
                row.q_m = one;
                row.q_o = minus_one;
                row.cells = [Some(args[0]), Some(args[1]), Some(node.wire)];
                rows.push(row);
                place(&mut wire_cells, index, Column::A, args[0]);
                place(&mut wire_cells, index, Column::B, args[1]);
                place(&mut wire_cells, index, Column::C, node.wire);
            }

            NodeOp::Neg { args } => {
                // -a - c = 0
                let mut row = Row::empty(format!("neg at wire {}", node.wire));
                row.q_l = minus_one;
                row.q_o = minus_one;
                row.cells = [Some(args[0]), None, Some(node.wire)];
                rows.push(row);
                place(&mut wire_cells, index, Column::A, args[0]);
                place(&mut wire_cells, index, Column::C, node.wire);
            }
        }
    }

    for assertion in &ir.assertions {
        // lhs - rhs = 0. The `c` cell stays empty, and q_O is zero with it.
        let index = rows.len();
        let mut row = Row::empty(format!("line {}: {}", assertion.line, assertion.label));
        row.q_l = one;
        row.q_r = minus_one;
        row.cells = [Some(assertion.lhs), Some(assertion.rhs), None];
        rows.push(row);
        place(&mut wire_cells, index, Column::A, assertion.lhs);
        place(&mut wire_cells, index, Column::B, assertion.rhs);
    }

    // A public input that no gate happens to mention still has to be bound to
    // a cell, or the verifier has nothing to point at. An all-zero row is
    // satisfied by any value, which is precisely what an unused input is.
    for input in &ir.inputs {
        if input.visibility.is_public() && !wire_cells.contains_key(&input.wire) {
            let index = rows.len();
            let mut row = Row::empty(format!("binding for public input '{}'", input.name));
            row.cells[Column::A.index()] = Some(input.wire);
            rows.push(row);
            place(&mut wire_cells, index, Column::A, input.wire);
        }
    }

    // Assert the wiring: every cell holding a given wire must agree with the
    // next. Chaining is enough — equality is transitive, and a chain costs
    // n-1 copies where relating every pair would cost n²/2.
    let mut copies: Vec<(Cell, Cell)> = Vec::new();
    let mut wires: Vec<&u32> = wire_cells.keys().collect();
    wires.sort();
    for wire in wires {
        let cells = &wire_cells[wire];
        for pair in cells.windows(2) {
            copies.push((pair[0], pair[1]));
        }
    }

    let public_cells = ir
        .inputs
        .iter()
        .filter(|input| input.visibility.is_public())
        .map(|input| {
            let cell = wire_cells[&input.wire][0];
            (input.wire, cell)
        })
        .collect();

    Ok(Plonkish { rows, copies, public_cells })
}