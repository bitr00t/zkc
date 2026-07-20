//! `zkc-prove` — the backend CLI.
//!
//! ```text
//! zkc-prove --ir build/iszero.ir.json --inputs inputs/iszero_honest.json
//! ```
//!
//! Pipeline: load IR → solve the witness → lower to R1CS → **check it
//! ourselves** → Groth16 setup, prove, verify.
//!
//! The self-check before proving is not redundant. A violated constraint gets
//! reported with the assertion's original source text and line number, which
//! is the kind of error a compiler owes its users; without it the same
//! failure surfaces as an assertion deep inside the proving library.

use std::collections::HashMap;
use std::process::ExitCode;

use ark_bn254::{Bn254, Fr};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;

use zkc_core::field::ZkField;
use zkc_core::ir::Ir;
use zkc_core::lower::lower;
use zkc_core::witness::{solve, SolveInputs};
use zkc_prove::LoweredCircuit;

struct Options {
    ir_path: String,
    inputs_path: String,
    verbose: bool,
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

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--ir" => ir_path = args.next(),
            "--inputs" => inputs_path = args.next(),
            "--verbose" => verbose = true,
            other => return Err(format!("unknown argument '{other}'")),
        }
    }
    Ok(Options {
        ir_path: ir_path.ok_or("missing --ir <file.ir.json>")?,
        inputs_path: inputs_path.ok_or("missing --inputs <file.json>")?,
        verbose,
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

    // 2. Choose the arithmetization.
    let r1cs = lower::<Fr>(&ir)?;
    let assignment = r1cs.assignment(&wire_values);

    println!(
        "circuit '{}': {} R1CS variables, {} constraints, {} public input(s)",
        ir.name,
        r1cs.num_vars,
        r1cs.constraints.len(),
        r1cs.public_vars.len()
    );
    if options.verbose {
        for (wire, name) in ir.advice_wires() {
            println!("  advice '{name}' -> wire {wire} = {}", wire_values[wire as usize].to_decimal());
        }
    }

    // 3. Check the assignment ourselves, with source-level error messages.
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

    // 4. Prove and verify.
    //
    // A deterministic RNG keeps the demo reproducible. A real deployment runs
    // a multi-party trusted setup precisely so that nobody knows this
    // randomness — whoever does can forge proofs for any statement.
    let mut rng = StdRng::seed_from_u64(42);
    let (proving_key, verifying_key) =
        Groth16::<Bn254>::circuit_specific_setup(LoweredCircuit::shape(r1cs.clone()), &mut rng)
            .map_err(|e| format!("setup failed: {e}"))?;

    let circuit = LoweredCircuit::assigned(r1cs, assignment);
    let public_inputs = circuit.public_inputs();
    let proof =
        Groth16::<Bn254>::prove(&proving_key, circuit, &mut rng).map_err(|e| format!("proving failed: {e}"))?;
    let accepted = Groth16::<Bn254>::verify(&verifying_key, &public_inputs, &proof)
        .map_err(|e| format!("verification failed: {e}"))?;

    let shown: Vec<String> = public_inputs.iter().map(|v| v.to_decimal()).collect();
    println!("public inputs: [{}]", shown.join(", "));
    println!("verifier accepts: {accepted}");

    Ok(if accepted { ExitCode::SUCCESS } else { ExitCode::FAILURE })
}