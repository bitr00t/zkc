//! Bridge from our lowered R1CS to arkworks' constraint system.
//!
//! Phases 1-3 borrow a proving backend rather than writing one: the point of
//! the walking skeleton is a complete source-file-to-proof pipeline, and
//! Groth16 over BN254 is the shortest path to that. Phase 5 replaces this
//! crate with a hand-written FRI/STARK prover; nothing else has to change,
//! because everything upstream stops at the arithmetization-neutral IR.

use ark_ff::PrimeField;
use ark_relations::R1CS::{
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