//! `zkc-profile` — per-source-line cost attribution (phase 6, Workstream L).
//!
//! ```text
//! zkc-profile build/iszero.ir.json [more.ir.json ...] [--json]
//! ```
//!
//! Where `zkc-stats` answers "how expensive is this circuit," `zkc-profile`
//! answers "which line is expensive." It lowers each IR to the unfused R1CS
//! and Plonkish arithmetizations and attributes every constraint and every row
//! to the source line that produced it, then ranks the lines by weight. The
//! per-line costs sum to exactly the unfused totals `zkc-stats` reports — this
//! is the same measurement, seen by line rather than in total.

use std::process::ExitCode;

use zkc_tools::stats::profile_json;

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
        match profile_json(&ir_json) {
            Ok(profile) => {
                if options.json {
                    println!("{}", profile.render_json());
                } else {
                    print!("{}", profile.render_text());
                    if options.paths.len() > 1 {
                        println!();
                    }
                }
            }
            Err(message) => {
                eprintln!("error: {path}: {message}");
                had_error = true;
            }
        }
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
    "zkc-profile — attribute a circuit's constraint/row cost to source lines\n\n\
     usage: zkc-profile <ir.json> [more.ir.json ...] [--json]\n\n\
     Ranks source lines by the R1CS constraints and Plonkish rows they produce\n\
     in the unfused arithmetization. The per-line costs sum to the unfused\n\
     totals zkc-stats reports. --json emits one object per line."
        .to_string()
}