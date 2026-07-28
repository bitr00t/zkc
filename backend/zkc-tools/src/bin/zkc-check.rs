//! `zkc-check` — lower an IR and check the witness against it.
//!
//! ```text
//! zkc-check --ir build/iszero.ir.json --inputs inputs/iszero_honest.json
//!           [--arith r1cs|plonkish]
//! ```
//!
//! Pipeline: load IR → solve the witness → lower to the chosen arithmetization
//! → **check it ourselves**.
//!
//! This was `zkc-prove`, and the last step used to be Groth16 setup / prove /
//! verify against a borrowed arkworks backend. Phase 5 wrote a prover of our
//! own, and the borrowed one has been superseded since; retiring it leaves the
//! part of this binary that was never about cryptography in the first place.
//! To prove a circuit, lower it and hand it to `zkc-core`'s STARK.
//!
//! What the tool is *for* is unchanged, and it is the phase-4 claim: a circuit
//! can be built either way, and the frontend's determinacy record is the same
//! on both paths, because soundness is a property of the IR and not of how it
//! is arithmetized. `--arith plonkish` lowers, validates and self-checks the
//! Plonkish circuit; `--arith r1cs` does the same for R1CS. Both print the same
//! determinacy line.
//!
//! The self-check is not redundant. A violated constraint gets reported with
//! the assertion's original source text and line number, which is the kind of
//! error a compiler owes its users; without it the same failure surfaces as an
//! assertion deep inside a proving library.

use std::collections::HashMap;
use std::process::ExitCode;

use ark_bn254::Fr;

use zkc_core::field::ZkField;
use zkc_core::ir::Ir;
use zkc_core::lower::lower;
use zkc_core::plonkish::lower_plonkish;
use zkc_core::witness::{solve, SolveInputs};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Arith {
    R1cs,
    Plonkish,
}

struct Options {
    ir_path: String,
    inputs_path: String,
    verbose: bool,
    arith: Arith,
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::FAILURE
        }
    }
}

fn parse_options() -> Result<Options, String> {
    let mut ir_path = None;
    let mut inputs_path = None;
    let mut verbose = false;
    let mut arith = Arith::R1cs;

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--ir" => ir_path = args.next(),
            "--inputs" => inputs_path = args.next(),
            "--verbose" => verbose = true,
            "--arith" => {
                arith = match args.next().as_deref() {
                    Some("r1cs") => Arith::R1cs,
                    Some("plonkish") => Arith::Plonkish,
                    Some(other) => return Err(format!("unknown arithmetization '{other}'; expected 'r1cs' or 'plonkish'")),
                    None => return Err("--arith expects 'r1cs' or 'plonkish'".to_string()),
                }
            }
            other => return Err(format!("unknown argument '{other}'")),
        }
    }
    Ok(Options {
        ir_path: ir_path.ok_or("missing --ir <file.ir.json>")?,
        inputs_path: inputs_path.ok_or("missing --inputs <file.json>")?,
        verbose,
        arith,
    })
}

/// Inputs file shape:
/// ```json
/// { "inputs": { "x": "5", "out": "0" }, "advice": { "inv": "0" } }
/// ```
/// `advice` is optional and models a prover that ignores the hint.
fn load_inputs(path: &str) -> Result<(HashMap<String, Fr>, HashMap<String, Fr>), String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("reading {path}: {e}"))?;
    let json: serde_json::Value =
        serde_json::from_str(&text).map_err(|e| format!("parsing {path}: {e}"))?;

    let section = |key: &str| -> Result<HashMap<String, Fr>, String> {
        let mut map = HashMap::new();
        if let Some(object) = json.get(key) {
            let entries = object
                .as_object()
                .ok_or_else(|| format!("'{key}' must be an object of name -> decimal string"))?;
            for (name, value) in entries {
                let decimal = value
                    .as_str()
                    .ok_or_else(|| format!("value for '{name}' must be a decimal string"))?;
                map.insert(name.clone(), Fr::from_decimal(decimal)?);
            }
        }
        Ok(map)
    };

    Ok((section("inputs")?, section("advice")?))
}

fn run() -> Result<ExitCode, String> {
    let options = parse_options()?;

    let ir_text =
        std::fs::read_to_string(&options.ir_path).map_err(|e| format!("reading IR: {e}"))?;
    let ir = Ir::from_json(&ir_text)?;
    if ir.field != "bn254" {
        return Err(format!(
            "this backend instantiates BN254, but the IR declares field '{}'",
            ir.field
        ));
    }

    let (inputs, advice_overrides) = load_inputs(&options.inputs_path)?;
    if !advice_overrides.is_empty() {
        let names: Vec<&str> = advice_overrides.keys().map(String::as_str).collect();
        println!("note: advice overridden by the prover: {}", names.join(", "));
    }

    // 1. Compute every wire value.
    let wire_values = solve(
        &ir,
        &SolveInputs { inputs: &inputs, advice_overrides: &advice_overrides },
    )?;

    // The determinacy record travels with the IR, unchanged by the choice
    // below — soundness is a property of the circuit, not of how it is
    // arithmetized. Report it before lowering so it is visibly independent.
    report_determinacy(&ir);

    // 2. Choose the arithmetization.
    match options.arith {
        Arith::R1cs => check_r1cs(&ir, &wire_values, options.verbose),
        Arith::Plonkish => build_plonkish(&ir, &wire_values, options.verbose),
    }
}

/// Show the frontend's soundness verdict, which both arithmetizations inherit.
fn report_determinacy(ir: &Ir) {
    let d = &ir.determinacy;
    if d.proved {
        println!(
            "determinacy: proved ({} output(s): {}), {} case(s) — inherited by any arithmetization",
            d.targets.len(),
            d.targets.join(", "),
            d.branches.len().max(1),
        );
    } else {
        println!("determinacy: NOT proved in the artifact (the frontend did not certify soundness)");
    }
}

/// The R1CS path: lower, then self-check the witness against the constraints.
fn check_r1cs(ir: &Ir, wire_values: &[Fr], verbose: bool) -> Result<ExitCode, String> {
    let r1cs = lower::<Fr>(ir)?;
    let assignment = r1cs.assignment(wire_values);

    println!(
        "arithmetization: R1CS — {} variables, {} constraints, {} public input(s)",
        r1cs.num_vars,
        r1cs.constraints.len(),
        r1cs.public_vars.len()
    );
    if verbose {
        for (wire, name) in ir.advice_wires() {
            println!("  advice '{name}' -> wire {wire} = {}", wire_values[wire as usize].to_decimal());
        }
    }

    let violations = r1cs.check(&assignment);
    if !violations.is_empty() {
        println!("\nconstraint system NOT satisfied — refusing to prove:");
        for violation in &violations {
            println!(
                "  [{}] {}\n      left-hand side = {}, right-hand side = {}",
                violation.index, violation.origin, violation.lhs, violation.rhs
            );
        }
        println!(
            "\nThe witness computes values the constraints reject. An honest prover\n\
             cannot turn this into a proof."
        );
        return Ok(ExitCode::FAILURE);
    }
    println!("self-check: all {} constraints satisfied", r1cs.constraints.len());

    let public_inputs: Vec<String> =
        r1cs.public_vars.iter().map(|var| assignment[*var].to_decimal()).collect();
    println!("public inputs: [{}]", public_inputs.join(", "));

    Ok(ExitCode::SUCCESS)
}

/// The Plonkish path: lower, validate the lowering, self-check the witness —
/// and stop. There is no Plonkish prover here; that is phase 5. This is the
/// exact counterpart of how R1CS entered in phase 0: a checked arithmetization
/// standing on its own, before any cryptography is bolted on.
fn build_plonkish(ir: &Ir, wire_values: &[Fr], verbose: bool) -> Result<ExitCode, String> {
    let circuit = lower_plonkish::<Fr>(ir)?;

    println!(
        "arithmetization: Plonkish — {} rows, {} columns, {} copy constraint(s), {} public input(s)",
        circuit.num_rows(),
        circuit.num_columns(),
        circuit.copies.len(),
        circuit.public_cells.len()
    );
    if verbose {
        for (wire, name) in ir.advice_wires() {
            println!("  advice '{name}' -> wire {wire} = {}", wire_values[wire as usize].to_decimal());
        }
    }

    // First: is the lowering itself well-formed? (Workstream E.1)
    if let Err(problems) = circuit.validate() {
        println!("\nthe Plonkish lowering is malformed — this is a compiler bug, not a bad witness:");
        for problem in &problems {
            println!("  {problem:?}");
        }
        return Ok(ExitCode::FAILURE);
    }

    // Then: does the witness satisfy it? (Workstream D.1 / E.1)
    let assignment = circuit.assignment(wire_values);
    let violations = circuit.check(&assignment);
    if !violations.is_empty() {
        println!("\nconstraint system NOT satisfied — the witness would not prove:");
        for violation in &violations {
            println!("  {}", violation.describe());
        }
        return Ok(ExitCode::FAILURE);
    }
    println!(
        "self-check: all {} gate(s) and {} copy constraint(s) satisfied",
        circuit.num_rows(),
        circuit.copies.len()
    );

    println!(
        "\nno Plonkish prover yet (phase 5): the circuit is lowered, validated and\n\
         satisfied, but not proved. The R1CS path takes it all the way to a proof."
    );
    Ok(ExitCode::SUCCESS)
}