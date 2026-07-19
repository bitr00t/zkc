//! R1CS: sparse linear combinations, constraints, and a satisfiability check.
//!
//! A constraint is `(a · z) * (b · z) = (c · z)` where `z` is the assignment
//! vector and `z[0] = 1`. The checker is kept in the backend deliberately:
//! before handing anything to a proving system we verify the assignment
//! ourselves, so a violated constraint is reported as a *source-level*
//! message (with the assertion's original text and line number) instead of
//! surfacing as an opaque panic inside the prover.

use crate::field::ZkField;

/// A sparse linear combination over assignment variables: `(var, coeff)`.
#[derive(Debug, Clone, PartialEq)]
pub struct Lc<F> {
    pub terms: Vec<(usize, F)>,
}

impl<F: ZkField> Lc<F> {
    pub fn zero() -> Self {
        Lc { terms: Vec::new() }
    }

    /// The constant `value`, expressed via the always-one variable 0.
    pub fn constant(value: F) -> Self {
        if value.is_zero() {
            Self::zero()
        } else {
            Lc { terms: vec![(0, value)] }
        }
    }

    pub fn var(index: usize) -> Self {
        Lc { terms: vec![(index, F::one())] }
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut terms = self.terms.clone();
        for (var, coeff) in &other.terms {
            match terms.iter_mut().find(|(v, _)| v == var) {
                Some((_, existing)) => *existing = existing.add(*coeff),
                None => terms.push((*var, *coeff)),
            }
        }
        terms.retain(|(_, coeff)| !coeff.is_zero());
        Lc { terms }
    }

    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.scale(F::one().neg()))
    }

    pub fn scale(&self, factor: F) -> Self {
        Lc {
            terms: self
                .terms
                .iter()
                .map(|(var, coeff)| (*var, coeff.mul(factor)))
                .filter(|(_, coeff)| !coeff.is_zero())
                .collect(),
        }
    }

    pub fn eval(&self, assignment: &[F]) -> F {
        self.terms
            .iter()
            .fold(F::zero(), |acc, (var, coeff)| acc.add(coeff.mul(assignment[*var])))
    }
}

#[derive(Debug, Clone)]
pub struct Constraint<F> {
    pub a: Lc<F>,
    pub b: Lc<F>,
    pub c: Lc<F>,
    /// Where this constraint came from, in the user's own words.
    pub origin: String,
}

#[derive(Debug, Clone)]
pub struct R1cs<F> {
    pub num_vars: usize,
    pub constraints: Vec<Constraint<F>>,
    /// Variables that are public inputs, in declaration order. This ordering
    /// is part of the contract with the verifier.
    pub public_vars: Vec<usize>,
    /// For each variable, the IR wire whose value it holds (variable 0 is the
    /// constant one and maps to nothing).
    pub var_to_wire: Vec<Option<u32>>,
}

#[derive(Debug, Clone)]
pub struct Violation {
    pub index: usize,
    pub origin: String,
    pub lhs: String,
    pub rhs: String,
}

impl<F: ZkField> R1cs<F> {
    /// Build the assignment vector from solved wire values.
    pub fn assignment(&self, wire_values: &[F]) -> Vec<F> {
        self.var_to_wire
            .iter()
            .map(|slot| match slot {
                None => F::one(),
                Some(wire) => wire_values[*wire as usize],
            })
            .collect()
    }

    pub fn check(&self, assignment: &[F]) -> Vec<Violation> {
        self.constraints
            .iter()
            .enumerate()
            .filter_map(|(index, constraint)| {
                let lhs = constraint.a.eval(assignment).mul(constraint.b.eval(assignment));
                let rhs = constraint.c.eval(assignment);
                if lhs == rhs {
                    None
                } else {
                    Some(Violation {
                        index,
                        origin: constraint.origin.clone(),
                        lhs: lhs.to_decimal(),
                        rhs: rhs.to_decimal(),
                    })
                }
            })
            .collect()
    }

    pub fn is_satisfied(&self, assignment: &[F]) -> bool {
        self.check(assignment).is_empty()
    }
}