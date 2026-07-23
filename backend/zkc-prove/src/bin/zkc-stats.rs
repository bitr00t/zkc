//! `zkc-stats` — arithmetization cost accounting (phase 4, Workstream F.1).
//!
//! ```text
//! zkc-stats build/iszero.ir.json [more.ir.json ...] [--json]
//! ```
//!
//! Loads one or more lowered IR files, measures each as both R1CS and
//! Plonkish, and prints the two bills side by side. This is the neutral IR
//! paying rent: the same graph, two arithmetizations, and a per-circuit answer
//! to which is cheaper — a measurement, not a preference.
//!
//! It shares nothing with the proving path but the crate: no Groth16, no
//! trusted setup, just lower-and-count. Cost is a property of the
//! arithmetization, available long before any cryptography.

use std::process::ExitCode;

use zkc_prove::stats::{measure_json, Cheaper};

struct Options {
    paths: Vec<String>,
    json: bool,
}

fn main() -> ExitCode {
    let options = match parse() {
        Ok(options) => options,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::FAILURE;
        }
    };

    let mut totals = (0usize, 0usize, 0usize); // r1cs, plonkish, ties/crossovers seen
    let mut had_error = false;

    for path in &options.paths {
        let ir_json = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(err) => {
                eprintln!("error: cannot read '{path}': {err}");
                had_error = true;
                continue;
            }
        };
        match measure_json(&ir_json) {
            Ok(report) => {
                if options.json {
                    println!("{}", report.render_json());
                } else {
                    print!("{}", report.render_text());
                    if options.paths.len() > 1 {
                        println!();
                    }
                }
                match report.cheaper() {
                    Cheaper::R1cs => totals.0 += 1,
                    Cheaper::Plonkish => totals.1 += 1,
                    Cheaper::Tie => totals.2 += 1,
                }
            }
            Err(message) => {
                eprintln!("error: {path}: {message}");
                had_error = true;
            }
        }
    }

    // A one-line summary when several circuits were measured, so the headline
    // — that neither arithmetization dominates — is visible at a glance.
    if !options.json && options.paths.len() > 1 {
        eprintln!(
            "summary: R1CS cheaper on {}, Plonkish on {}, tied on {}",
            totals.0, totals.1, totals.2
        );
    }

    if had_error {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn parse() -> Result<Options, String> {
    let mut paths = Vec::new();
    let mut json = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--json" => json = true,
            "-h" | "--help" => return Err(usage()),
            flag if flag.starts_with('-') => {
                return Err(format!("unknown option '{flag}'\n{}", usage()));
            }
            _ => paths.push(arg),
        }
    }
    if paths.is_empty() {
        return Err(usage());
    }
    Ok(Options { paths, json })
}

fn usage() -> String {
    "zkc-stats — compare R1CS and Plonkish cost for a lowered circuit\n\n\
     usage: zkc-stats <ir.json> [more.ir.json ...] [--json]\n\n\
     Prints, per circuit, the R1CS constraint count and the Plonkish row count\n\
     (both fused and unfused), the copy-constraint cost Plonkish alone pays,\n\
     and which arithmetization is cheaper. --json emits one object per line."
        .to_string()
}