//! `zkc-core` — everything between the compiler frontend and a proving system.
//!
//! Loads the serialized Core IR, solves witnesses, lowers to R1CS and checks
//! satisfiability. It is generic over the field and contains no cryptography:
//! swapping arkworks/Groth16 for a hand-written FRI prover (phase 5) does not
//! touch this crate, only which backend consumes its output.

pub mod field;
pub mod air;
pub mod fft;
pub mod fri;
pub mod goldilocks;
pub mod hash;
pub mod merkle;
pub mod stark;
pub mod transcript;
pub mod ir;
pub mod lower;
pub mod plonkish;
pub mod r1cs;
pub mod witness;

pub use field::ZkField;
pub use ir::Ir;