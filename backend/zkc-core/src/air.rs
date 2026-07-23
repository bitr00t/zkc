//! Plonkish as AIR-style polynomial constraints (phase 5, Workstream I.1).
//!
//! Phase 4 built a Plonkish table: rows carrying five selectors and three
//! witness cells, a gate identity per row, and copy constraints tying shared
//! cells together. A STARK proves exactly this shape — that is why phase 4
//! chose Plonkish — but it proves it as *polynomials*, not as a table checked
//! row by row. This module is the translation.
//!
//! ## The gate identity becomes one polynomial constraint
//!
//! Interpolate each column over a domain `H` of `n` rows (the size-`n`
//! multiplicative subgroup): the three witness columns `a, b, c` and the five
//! selectors `q_L, q_R, q_O, q_M, q_C` each become a polynomial. The gate
//! identity, which phase 4 evaluated at each row, becomes a single polynomial:
//!
//! ```text
//!   C(x) = q_L(x)·a(x) + q_R(x)·b(x) + q_O(x)·c(x) + q_M(x)·a(x)·b(x) + q_C(x)
//! ```
//!
//! "The gate holds on every row" is exactly "`C` vanishes on all of `H`", which
//! is exactly "`C` is divisible by the vanishing polynomial `Z_H(x) = x^n - 1`".
//! The quotient `Q = C / Z_H` is a polynomial iff the circuit is satisfied, and
//! FRI proving `Q` has low degree is what proves the circuit — that is the STARK
//! (Workstream I.2). This module produces the pieces `C` is built from.
//!
//! ## The copy constraints become a permutation
//!
//! The wiring has no counterpart in the gate identity; in a STARK it is a
//! permutation argument. Each witness cell has a position; the copy constraints
//! partition positions into classes that must hold equal values; a permutation
//! `σ` that cycles each class witnesses the partition. This module *builds* `σ`
//! from the copy constraints, the data a grand-product permutation argument
//! consumes. Enforcing it in the proof is the layer above; see the note in
//! `stark.rs` on what the gate constraint alone already catches.
//!
//! Fixed data only. The witness is separate ([`Trace`]), because the selectors
//! and the wiring are properties of the circuit while `a, b, c` are the
//! prover's secret — the same split R1CS draws between its matrices and its
//! assignment.

use crate::field::ZkField;
use crate::plonkish::{Cell, Column, Plonkish};

/// The fixed, circuit-derived part of the arithmetization: selectors, wiring
/// permutation, and public-input positions, all over a power-of-two domain.
pub struct Air<F> {
    /// Domain size: rows padded to the next power of two, so an FFT exists.
    pub n: usize,
    /// The five selector columns, each length `n`, padded rows all-zero.
    pub q_l: Vec<F>,
    pub q_r: Vec<F>,
    pub q_o: Vec<F>,
    pub q_m: Vec<F>,
    pub q_c: Vec<F>,
    /// The wiring permutation on cell positions (see [`cell_position`]).
    /// `sigma[p]` is the next position in `p`'s equality class.
    pub sigma: Vec<usize>,
    /// Public inputs: `(claimed-value wire, cell position)`, binding order kept.
    pub public_positions: Vec<(u32, usize)>,
}

/// The prover's secret: the three witness columns over the same domain.
pub struct Trace<F> {
    pub a: Vec<F>,
    pub b: Vec<F>,
    pub c: Vec<F>,
}

/// The flat position of a cell: column-major over the padded domain, so column
/// `k` occupies positions `[k·n, (k+1)·n)`. A single index space is what lets
/// the permutation `σ` cross columns.
pub fn cell_position(cell: Cell, n: usize) -> usize {
    cell.column.index() * n + cell.row
}

impl<F: ZkField> Air<F> {
    /// Extract the fixed arithmetization from a lowered Plonkish circuit.
    pub fn from_plonkish(circuit: &Plonkish<F>) -> Self {
        let rows = circuit.num_rows();
        let n = rows.max(1).next_power_of_two();

        let mut q_l = vec![F::zero(); n];
        let mut q_r = vec![F::zero(); n];
        let mut q_o = vec![F::zero(); n];
        let mut q_m = vec![F::zero(); n];
        let mut q_c = vec![F::zero(); n];
        for (i, row) in circuit.rows.iter().enumerate() {
            q_l[i] = row.q_l;
            q_r[i] = row.q_r;
            q_o[i] = row.q_o;
            q_m[i] = row.q_m;
            q_c[i] = row.q_c;
        }

        // Build σ from the copy constraints. Union the positions each copy ties
        // together into equality classes, then make σ a single cycle per class.
        let total = 3 * n;
        let mut parent: Vec<usize> = (0..total).collect();
        fn find(parent: &mut [usize], x: usize) -> usize {
            let mut root = x;
            while parent[root] != root {
                root = parent[root];
            }
            let mut cur = x;
            while parent[cur] != root {
                let next = parent[cur];
                parent[cur] = root;
                cur = next;
            }
            root
        }
        for (left, right) in &circuit.copies {
            let pl = cell_position(*left, n);
            let pr = cell_position(*right, n);
            let (rl, rr) = (find(&mut parent, pl), find(&mut parent, pr));
            if rl != rr {
                parent[rl] = rr;
            }
        }
        // Group positions by class root, then cycle each class.
        let mut classes: std::collections::HashMap<usize, Vec<usize>> = std::collections::HashMap::new();
        for p in 0..total {
            let root = find(&mut parent, p);
            classes.entry(root).or_default().push(p);
        }
        let mut sigma: Vec<usize> = (0..total).collect();
        for members in classes.values() {
            let k = members.len();
            for i in 0..k {
                sigma[members[i]] = members[(i + 1) % k];
            }
        }

        let public_positions = circuit
            .public_cells
            .iter()
            .map(|(wire, cell)| (*wire, cell_position(*cell, n)))
            .collect();

        Air { n, q_l, q_r, q_o, q_m, q_c, sigma, public_positions }
    }

    /// The witness columns over the padded domain, from solved wire values.
    pub fn trace(circuit: &Plonkish<F>, wire_values: &[F]) -> Trace<F> {
        let assignment = circuit.assignment(wire_values);
        let n = circuit.num_rows().max(1).next_power_of_two();
        let mut a = vec![F::zero(); n];
        let mut b = vec![F::zero(); n];
        let mut c = vec![F::zero(); n];
        for (i, row) in assignment.iter().enumerate() {
            a[i] = row[Column::A.index()];
            b[i] = row[Column::B.index()];
            c[i] = row[Column::C.index()];
        }
        Trace { a, b, c }
    }

    /// Evaluate the gate identity from column values at one point. Zero means
    /// the gate holds there.
    pub fn gate_identity(&self, a: F, b: F, c: F, ql: F, qr: F, qo: F, qm: F, qc: F) -> F {
        ql.mul(a)
            .add(qr.mul(b))
            .add(qo.mul(c))
            .add(qm.mul(a).mul(b))
            .add(qc)
    }

    /// The three coset representatives that keep the columns' label ranges
    /// disjoint: column `j`'s identity labels live in `k[j] · <ω>`, and the
    /// three cosets `1·H`, `7·H`, `49·H` do not overlap (7 and 49 are not in
    /// the tiny subgroup `H`). This is what makes the permutation over all
    /// `3n` positions well-defined as a single label space.
    pub fn column_reps() -> [F; 3] {
        [F::one(), F::from_u64(7), F::from_u64(49)]
    }

    /// The identity and permutation label evaluations on `H`, per column.
    ///
    /// `id[j][i]` is the label of cell `(column j, row i)`; `sigma[j][i]` is the
    /// label of the cell that cell is wired to. A grand-product argument over
    /// the two multisets forces wired cells to hold equal values — this is the
    /// data it consumes.
    pub fn permutation_label_evals(&self, omega_powers: &[F]) -> ([Vec<F>; 3], [Vec<F>; 3]) {
        let n = self.n;
        let k = Self::column_reps();
        let mut id = [vec![F::zero(); n], vec![F::zero(); n], vec![F::zero(); n]];
        let mut sigma = [vec![F::zero(); n], vec![F::zero(); n], vec![F::zero(); n]];
        for j in 0..3 {
            for i in 0..n {
                id[j][i] = k[j].mul(omega_powers[i]);
                let target = self.sigma[j * n + i];
                let (tcol, trow) = (target / n, target % n);
                sigma[j][i] = k[tcol].mul(omega_powers[trow]);
            }
        }
        (id, sigma)
    }
}