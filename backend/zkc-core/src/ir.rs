//! Loading and validating the serialized Core IR.
//!
//! This is the Haskell/Rust boundary. The format is versioned and its
//! invariants are *checked here* rather than assumed: a backend that trusts
//! its frontend blindly turns frontend bugs into miscompiled circuits, and in
//! this domain a miscompiled circuit is a security hole.

use serde::Deserialize;
use std::collections::HashSet;

pub const SUPPORTED_SCHEMA_VERSION: u32 = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Visibility {
    Private,
    /// A verifier-visible *input*. The prover supplies it; nothing requires
    /// it to be determined by anything else.
    Public,
    /// A verifier-visible value the circuit *computes*. The frontend has
    /// proved it is a function of the inputs — see [`Determinacy`].
    Output,
}

impl Visibility {
    /// Both `Public` and `Output` end up in the verifier's public input
    /// vector; they differ only in the proof obligation the frontend
    /// discharged, which is a frontend concern.
    pub fn is_public(self) -> bool {
        matches!(self, Visibility::Public | Visibility::Output)
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct Input {
    pub wire: u32,
    pub name: String,
    pub visibility: Visibility,
    #[serde(default)]
    pub line: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HintKind {
    InvOrZero,
    Inv,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "op", rename_all = "lowercase")]
pub enum NodeOp {
    Const { value: String },
    Add { args: Vec<u32> },
    Sub { args: Vec<u32> },
    Mul { args: Vec<u32> },
    Neg { args: Vec<u32> },
    Hint {
        hint: HintKind,
        name: String,
        /// Which `gadget` block the advice was quarantined in. Advice is
        /// illegal outside one, so every hint has a gadget to point at.
        #[serde(default)]
        gadget: String,
        #[serde(default)]
        line: u32,
        args: Vec<u32>,
    },
}

impl NodeOp {
    pub fn args(&self) -> &[u32] {
        match self {
            NodeOp::Const { .. } => &[],
            NodeOp::Add { args }
            | NodeOp::Sub { args }
            | NodeOp::Mul { args }
            | NodeOp::Neg { args }
            | NodeOp::Hint { args, .. } => args,
        }
    }

    pub fn expected_arity(&self) -> usize {
        match self {
            NodeOp::Const { .. } => 0,
            NodeOp::Neg { .. } | NodeOp::Hint { .. } => 1,
            NodeOp::Add { .. } | NodeOp::Sub { .. } | NodeOp::Mul { .. } => 2,
        }
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct Node {
    pub wire: u32,
    /// Whether this wire's value depends, transitively, on a hint.
    ///
    /// This is the frontend's *syntactic* taint, not a soundness verdict: a
    /// tainted wire may be perfectly determined. Kept because it is useful
    /// for diagnostics and for future arithmetization choices.
    #[serde(default)]
    pub advice_derived: bool,
    #[serde(flatten)]
    pub op: NodeOp,
}

/// The frontend's determinacy proof, carried inside the artifact.
///
/// This is the point of schema v2. Soundness is not a property of "we used a
/// good compiler" — it is a claim about *this* circuit, so it travels with
/// it, and the backend refuses to prove anything whose obligations were not
/// discharged. A hand-written or tampered IR cannot skip the check by simply
/// omitting the record: `serde` defaults `proved` to false.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct Determinacy {
    #[serde(default)]
    pub proved: bool,
    #[serde(default)]
    pub targets: Vec<String>,
    /// The case splits the proof rested on, rendered for humans
    /// (e.g. `["x != 0"]`).
    #[serde(default)]
    pub branches: Vec<Vec<String>>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Assertion {
    pub lhs: u32,
    pub rhs: u32,
    pub label: String,
    pub line: u32,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Ir {
    pub schema_version: u32,
    pub name: String,
    pub field: String,
    pub const_one_wire: u32,
    pub inputs: Vec<Input>,
    pub nodes: Vec<Node>,
    pub assertions: Vec<Assertion>,
    #[serde(default)]
    pub determinacy: Determinacy,
}

impl Ir {
    pub fn from_json(text: &str) -> Result<Self, String> {
        let ir: Ir = serde_json::from_str(text).map_err(|e| format!("malformed IR JSON: {e}"))?;
        ir.validate()?;
        Ok(ir)
    }

    /// Total number of wires, including the constant-one wire.
    pub fn wire_count(&self) -> usize {
        1 + self.inputs.len() + self.nodes.len()
    }

    /// Enforce every invariant the lowering and solver rely on.
    pub fn validate(&self) -> Result<(), String> {
        if self.schema_version != SUPPORTED_SCHEMA_VERSION {
            return Err(format!(
                "unsupported IR schema version {} (this backend speaks {})",
                self.schema_version, SUPPORTED_SCHEMA_VERSION
            ));
        }
        // The soundness gate. An IR whose outputs were not proved determined
        // describes a circuit where the prover may choose what to prove, so
        // there is no honest reason to build a proving key for it.
        if !self.determinacy.proved && self.inputs.iter().any(|i| i.visibility == Visibility::Output) {
            return Err(format!(
                "circuit '{}' declares outputs but carries no discharged determinacy proof; \
                 refusing to prove it (recompile with a frontend that proves determinacy)",
                self.name
            ));
        }
        if self.const_one_wire != 0 {
            return Err("const_one_wire must be 0".into());
        }

        // Inputs occupy wires 1..=n, in order.
        for (index, input) in self.inputs.iter().enumerate() {
            let expected = index as u32 + 1;
            if input.wire != expected {
                return Err(format!(
                    "input '{}' has wire {} but inputs must occupy wires 1..=n in order (expected {})",
                    input.name, input.wire, expected
                ));
            }
        }

        // Nodes continue densely and in topological order: every argument
        // must refer to a strictly earlier wire.
        let first_node_wire = self.inputs.len() as u32 + 1;
        for (index, node) in self.nodes.iter().enumerate() {
            let expected = first_node_wire + index as u32;
            if node.wire != expected {
                return Err(format!(
                    "node {index} has wire {} but nodes must be dense and ordered (expected {expected})",
                    node.wire
                ));
            }
            if node.op.args().len() != node.op.expected_arity() {
                return Err(format!(
                    "node at wire {} has {} arguments, expected {}",
                    node.wire,
                    node.op.args().len(),
                    node.op.expected_arity()
                ));
            }
            for &arg in node.op.args() {
                if arg >= node.wire {
                    return Err(format!(
                        "node at wire {} references wire {arg}, which is not strictly earlier \
                         (the IR must be topologically ordered)",
                        node.wire
                    ));
                }
            }
        }

        let max_wire = self.wire_count() as u32;
        for assertion in &self.assertions {
            for wire in [assertion.lhs, assertion.rhs] {
                if wire >= max_wire {
                    return Err(format!(
                        "assertion on line {} references unknown wire {wire}",
                        assertion.line
                    ));
                }
            }
        }

        let mut seen = HashSet::new();
        for input in &self.inputs {
            if !seen.insert(input.name.as_str()) {
                return Err(format!("duplicate input name '{}'", input.name));
            }
        }
        Ok(())
    }

    /// Wires produced by hints, paired with their source-level names.
    pub fn advice_wires(&self) -> Vec<(u32, &str)> {
        self.nodes
            .iter()
            .filter_map(|node| match &node.op {
                NodeOp::Hint { name, .. } => Some((node.wire, name.as_str())),
                _ => None,
            })
            .collect()
    }
}