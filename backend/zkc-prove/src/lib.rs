//! Bridge from our lowered R1CS to arkworks' constraint system.
//!
//! Phases 1-3 borrow a proving backend rather than writing one: the point of
//! the walking skeleton is a complete source-file-to-proof pipeline, and
//! Groth16 over BN254 is the shortest path to that. Phase 5 replaces this
//! crate with a hand-written FRI/STARK prover; nothing else has to change,
//! because everything upstream stops at the arithmetization-neutral IR.

use ark_ff::PrimeField;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};

use zkc_core::r1cs::{Lc, R1cs};

pub struct LoweredCircuit<F: PrimeField> {
    pub r1cs: R1cs<F>,
    /// Full assignment (variable 0 first). `None` during setup, which only
    /// needs the circuit's *shape*.
    pub assignment: Option<Vec<F>>,
}

impl<F: PrimeField> LoweredCircuit<F> {
    pub fn shape(r1cs: R1cs<F>) -> Self {
        Self { r1cs, assignment: None }
    }

    pub fn assigned(r1cs: R1cs<F>, assignment: Vec<F>) -> Self {
        Self { r1cs, assignment: Some(assignment) }
    }

    /// The public inputs a verifier receives, in declaration order.
    pub fn public_inputs(&self) -> Vec<F> {
        let assignment = self.assignment.as_ref().expect("assigned circuit");
        self.r1cs.public_vars.iter().map(|var| assignment[*var]).collect()
    }
}

fn translate<F: PrimeField>(lc: &Lc<F>, vars: &[Variable]) -> LinearCombination<F> {
    let mut out = LinearCombination::zero();
    for (var, coeff) in &lc.terms {
        out = out + (*coeff, vars[*var]);
    }
    out
}

impl<F: PrimeField> ConstraintSynthesizer<F> for LoweredCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let mut vars: Vec<Variable> = Vec::with_capacity(self.r1cs.num_vars);
        vars.push(Variable::One);

        for index in 1..self.r1cs.num_vars {
            let value = || {
                self.assignment
                    .as_ref()
                    .map(|a| a[index])
                    .ok_or(SynthesisError::AssignmentMissing)
            };
            // Allocation order fixes the public-input ordering, which is part
            // of the contract with the verifier.
            let variable = if self.r1cs.public_vars.contains(&index) {
                cs.new_input_variable(value)?
            } else {
                cs.new_witness_variable(value)?
            };
            vars.push(variable);
        }

        for constraint in &self.r1cs.constraints {
            cs.enforce_constraint(
                translate(&constraint.a, &vars),
                translate(&constraint.b, &vars),
                translate(&constraint.c, &vars),
            )?;
        }
        Ok(())
    }
}
/// Arithmetization cost accounting (phase 4, Workstream F.1).
///
/// The neutral IR earns its keep here: the same graph is lowered two ways and
/// the two bills are put side by side. Nothing about this is a preference —
/// it is a measurement, and it is the first time the compiler can answer
/// "which arithmetization is cheaper for *this* circuit" with a number.
pub mod stats {
    use zkc_core::field::ZkField;
    use zkc_core::ir::{Ir, NodeOp};
    use zkc_core::lower::{lower, lower_with};
    use zkc_core::plonkish::lower_plonkish_with;

    /// The cost of one arithmetization, fused and unfused, plus the structural
    /// counts the two share.
    pub struct Report {
        pub name: String,
        pub field: String,
        // Shared IR shape.
        pub inputs: usize,
        pub public_inputs: usize,
        pub nodes: usize,
        pub multiplications: usize,
        pub hints: usize,
        pub assertions: usize,
        // R1CS.
        pub r1cs_constraints_unfused: usize,
        pub r1cs_constraints: usize,
        pub r1cs_variables: usize,
        // Plonkish.
        pub plonkish_rows_unfused: usize,
        pub plonkish_rows: usize,
        pub plonkish_copies: usize,
        pub plonkish_columns: usize,
    }

    /// Measure both arithmetizations of an IR over the field `F`.
    ///
    /// Lowering needs a concrete field even to count — a `const` node turns
    /// its decimal into a field element — but the counts themselves do not
    /// depend on which field, so any `F` gives the same table.
    pub fn measure<F: ZkField>(ir: &Ir) -> Result<Report, String> {
        let r1cs_unfused = lower_with::<F>(ir, false)?;
        let r1cs = lower::<F>(ir)?;
        let plonk_unfused = lower_plonkish_with::<F>(ir, false)?;
        let plonk = lower_plonkish_with::<F>(ir, true)?;

        let multiplications = ir
            .nodes
            .iter()
            .filter(|n| matches!(n.op, NodeOp::Mul { .. }))
            .count();
        let hints = ir
            .nodes
            .iter()
            .filter(|n| matches!(n.op, NodeOp::Hint { .. }))
            .count();
        let public_inputs = ir.inputs.iter().filter(|i| i.visibility.is_public()).count();

        Ok(Report {
            name: ir.name.clone(),
            field: ir.field.clone(),
            inputs: ir.inputs.len(),
            public_inputs,
            nodes: ir.nodes.len(),
            multiplications,
            hints,
            assertions: ir.assertions.len(),
            r1cs_constraints_unfused: r1cs_unfused.constraints.len(),
            r1cs_constraints: r1cs.constraints.len(),
            r1cs_variables: r1cs.num_vars,
            plonkish_rows_unfused: plonk_unfused.num_rows(),
            plonkish_rows: plonk.num_rows(),
            plonkish_copies: plonk.copies.len(),
            plonkish_columns: plonk.num_columns(),
        })
    }

    impl Report {
        /// Fraction of R1CS constraints fusion removed, in [0, 1].
        pub fn r1cs_fusion_saving(&self) -> f64 {
            saving(self.r1cs_constraints_unfused, self.r1cs_constraints)
        }

        /// Fraction of Plonkish rows fusion removed, in [0, 1].
        pub fn plonkish_fusion_saving(&self) -> f64 {
            saving(self.plonkish_rows_unfused, self.plonkish_rows)
        }

        /// Which arithmetization is cheaper on this circuit, if either.
        ///
        /// The whole point of the neutral IR is that this is a genuine
        /// question with a per-circuit answer, not a fixed property of the
        /// compiler.
        pub fn cheaper(&self) -> Cheaper {
            use std::cmp::Ordering::*;
            match self.r1cs_constraints.cmp(&self.plonkish_rows) {
                Less => Cheaper::R1cs,
                Greater => Cheaper::Plonkish,
                Equal => Cheaper::Tie,
            }
        }

        /// A human-readable block, in the style of the frontend's `--explain`.
        pub fn render_text(&self) -> String {
            let mut out = String::new();
            out.push_str(&format!("cost of '{}' over {}\n", self.name, self.field));
            out.push_str(&format!(
                "  circuit: {} inputs ({} public), {} nodes ({} mul, {} hint), {} assertions\n",
                self.inputs, self.public_inputs, self.nodes,
                self.multiplications, self.hints, self.assertions
            ));
            out.push_str(&format!(
                "  R1CS:     {:>4} constraints  ({} unfused, fusion -{:.0}%),  {} variables\n",
                self.r1cs_constraints, self.r1cs_constraints_unfused,
                self.r1cs_fusion_saving() * 100.0, self.r1cs_variables
            ));
            out.push_str(&format!(
                "  Plonkish: {:>4} rows         ({} unfused, fusion -{:.0}%),  {} copy constraints, {} columns\n",
                self.plonkish_rows, self.plonkish_rows_unfused,
                self.plonkish_fusion_saving() * 100.0, self.plonkish_copies, self.plonkish_columns
            ));
            out.push_str(&format!("  cheaper here: {}\n", self.cheaper().describe()));
            out
        }

        /// A machine-readable line, for diffing across runs or against Circom.
        pub fn render_json(&self) -> String {
            format!(
                "{{\"name\":\"{}\",\"field\":\"{}\",\
                 \"inputs\":{},\"public_inputs\":{},\"nodes\":{},\"multiplications\":{},\
                 \"hints\":{},\"assertions\":{},\
                 \"r1cs\":{{\"constraints\":{},\"constraints_unfused\":{},\"variables\":{}}},\
                 \"plonkish\":{{\"rows\":{},\"rows_unfused\":{},\"copies\":{},\"columns\":{}}},\
                 \"cheaper\":\"{}\"}}",
                self.name, self.field, self.inputs, self.public_inputs, self.nodes,
                self.multiplications, self.hints, self.assertions,
                self.r1cs_constraints, self.r1cs_constraints_unfused, self.r1cs_variables,
                self.plonkish_rows, self.plonkish_rows_unfused, self.plonkish_copies,
                self.plonkish_columns, self.cheaper().tag()
            )
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Cheaper {
        R1cs,
        Plonkish,
        Tie,
    }

    impl Cheaper {
        pub fn tag(self) -> &'static str {
            match self {
                Cheaper::R1cs => "r1cs",
                Cheaper::Plonkish => "plonkish",
                Cheaper::Tie => "tie",
            }
        }
        pub fn describe(self) -> &'static str {
            match self {
                Cheaper::R1cs => "R1CS (fewer constraints than Plonkish rows)",
                Cheaper::Plonkish => "Plonkish (fewer rows than R1CS constraints)",
                Cheaper::Tie => "tie (equal cost)",
            }
        }
    }

    fn saving(before: usize, after: usize) -> f64 {
        if before == 0 {
            0.0
        } else {
            1.0 - (after as f64) / (before as f64)
        }
    }

    /// One source line's share of the cost, in the unfused arithmetization
    /// where every constraint and row maps 1:1 to the construct that produced
    /// it.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct LineCost {
        pub line: u32,
        pub r1cs: usize,
        pub plonkish: usize,
    }

    /// A circuit's cost attributed to its source lines, ranked by weight.
    pub struct Profile {
        pub name: String,
        pub field: String,
        /// Per line, heaviest first (R1CS + Plonkish), ties broken by line.
        pub lines: Vec<LineCost>,
        /// Totals — equal to the *unfused* counts `measure`/`zkc-stats` report.
        /// Reproducing them by summing the per-line costs is the invariant the
        /// attribution must preserve.
        pub r1cs_total: usize,
        pub plonkish_total: usize,
    }

    /// Attribute a circuit's cost to its source lines.
    ///
    /// The counts come from the *unfused* lowering, where each R1CS constraint
    /// and each Plonkish row comes from exactly one source construct — so
    /// summing the per-line costs reproduces the unfused totals exactly.
    /// Fusion is a cross-line rewrite with no honest per-line split, so it is
    /// deliberately not what the profile attributes: "how expensive is this
    /// line" is a question about the base arithmetization.
    pub fn profile<F: ZkField>(ir: &Ir) -> Result<Profile, String> {
        use std::collections::BTreeMap;

        let r1cs = lower_with::<F>(ir, false)?;
        let plonk = lower_plonkish_with::<F>(ir, false)?;

        let mut by_line: BTreeMap<u32, (usize, usize)> = BTreeMap::new();
        for constraint in &r1cs.constraints {
            by_line.entry(constraint.line).or_default().0 += 1;
        }
        for row in &plonk.rows {
            by_line.entry(row.line).or_default().1 += 1;
        }

        let mut lines: Vec<LineCost> = by_line
            .into_iter()
            .map(|(line, (r1cs, plonkish))| LineCost { line, r1cs, plonkish })
            .collect();
        lines.sort_by(|a, b| {
            (b.r1cs + b.plonkish)
                .cmp(&(a.r1cs + a.plonkish))
                .then(a.line.cmp(&b.line))
        });

        Ok(Profile {
            name: ir.name.clone(),
            field: ir.field.clone(),
            r1cs_total: r1cs.constraints.len(),
            plonkish_total: plonk.rows.len(),
            lines,
        })
    }

    /// Convenience: profile from IR JSON over BN254.
    pub fn profile_json(ir_json: &str) -> Result<Profile, String> {
        let ir = Ir::from_json(ir_json)?;
        profile::<ark_bn254::Fr>(&ir)
    }

    impl Profile {
        /// The line carrying the most total cost, if any.
        pub fn hottest(&self) -> Option<&LineCost> {
            self.lines.first()
        }

        /// A human-readable ranking, in the style of `zkc-stats`'s report.
        /// Lines with a known source position come first, heaviest on top; a
        /// final row for any cost the frontend could not attribute (line 0).
        pub fn render_text(&self) -> String {
            let mut out = String::new();
            out.push_str(&format!(
                "cost of '{}' over {}, by source line (unfused)\n",
                self.name, self.field
            ));
            out.push_str("  line    R1CS  Plonkish\n");
            for cost in &self.lines {
                let label = if cost.line == 0 {
                    "  (n/a)".to_string()
                } else {
                    format!("  {:>4}", cost.line)
                };
                out.push_str(&format!(
                    "{}  {:>6}  {:>8}\n",
                    label, cost.r1cs, cost.plonkish
                ));
            }
            out.push_str(&format!(
                "  ----  {:>6}  {:>8}\n",
                self.r1cs_total, self.plonkish_total
            ));
            if let Some(hot) = self.hottest() {
                if hot.line != 0 {
                    out.push_str(&format!(
                        "  hottest: line {} ({} constraints, {} rows)\n",
                        hot.line, hot.r1cs, hot.plonkish
                    ));
                }
            }
            out
        }

        /// A machine-readable line, for the editor and for diffing across runs.
        pub fn render_json(&self) -> String {
            let lines: Vec<String> = self
                .lines
                .iter()
                .map(|c| {
                    format!(
                        "{{\"line\":{},\"r1cs\":{},\"plonkish\":{}}}",
                        c.line, c.r1cs, c.plonkish
                    )
                })
                .collect();
            format!(
                "{{\"name\":\"{}\",\"field\":\"{}\",\"lines\":[{}],\
                 \"r1cs_total\":{},\"plonkish_total\":{}}}",
                self.name,
                self.field,
                lines.join(","),
                self.r1cs_total,
                self.plonkish_total
            )
        }
    }

    /// Convenience for the CLI and tests: measure from IR JSON over BN254.
    pub fn measure_json(ir_json: &str) -> Result<Report, String> {
        let ir = Ir::from_json(ir_json)?;
        measure::<ark_bn254::Fr>(&ir)
    }
}