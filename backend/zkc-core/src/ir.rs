//! Loading and validating the serialized Core IR.
//!
//! This is the Haskell/Rust boundary. The format is versioned and its
//! invariants are *checked here* rather than assumed: a backend that trusts
//! its frontend blindly turns frontend bugs into miscompiled circuits, and in
//! this domain a miscompiled circuit is a security hole.

use serde::Deserialize;
use std::collections::HashSet;

pub const SUPPORTED_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Visibility {
    Private,
    Public,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Input {
    pub wire: u32,
    pub name: String,
    pub visibility: Visibility,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HintKind {
    InvOrZero,
    Inv,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag="op", rename_all = "lowercase")]
pub enum NodeOp {
    Const { value: String },
    Add { args: Vec<u32> },
    Sub { args: Vec<u32> },
    Mul { args: Vec<u32> },
    Neg { args: Vec<u32> },
    Hint { hint: HintKind, name: String, args: Vec<u32> },
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
    #[serde(flatten)]
    pub op: NodeOp,
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