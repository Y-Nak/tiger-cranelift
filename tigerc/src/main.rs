use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

use clap::{App, Arg};
use tigerc::prelude::*;

pub fn main() {
    let matches = App::new("tigerc")
        .arg(Arg::with_name("file").index(1).required(true))
        .arg(
            Arg::with_name("output_path")
                .default_value("./a.out")
                .short("o")
                .help("Specify output file name")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("dump_clif")
                .short("d")
                .help("Dump cranlift IR"),
        )
        .get_matches();

    let file = match matches.value_of("file") {
        Some(value) => PathBuf::from(value),
        _ => {
            eprintln!("No input files");
            return;
        }
    };

    let opts = Opts {
        output_path: PathBuf::from(matches.value_of("output_path").unwrap()),
        dump_clif: matches.is_present("dump_clif"),
    };

    let code = match fs::read_to_string(file) {
        Ok(value) => value,
        Err(e) => {
            eprintln!("{}", e);
            return;
        }
    };

    // Build ast.
    let mut parser = Parser::new(code.as_bytes()).unwrap();
    let mut expr = parser.parse().unwrap();

    // Semantic analysis.
    let mut semantic_analyzer = SemanticAnalyzer::new();
    semantic_analyzer.analyze_expr(&mut expr).unwrap();

    // Lambda lifting.
    let lifter = LambdaLifter::new();
    let functions = lifter.lift_functions(expr);

    // Generate object file.
    let code_generator = CodeGen::new(opts.clone());
    let object_file = code_generator.gen_code(&functions);
    let object_file = object_file.emit().unwrap();

    fs::File::create("target/tmp.o")
        .unwrap()
        .write_all(&object_file)
        .unwrap();

    Command::new("cc")
        .args(&[
            "target/tmp.o",
            "target/debug/libtiger_runtime.a",
            "-pthread",
            "-ldl",
        ])
        .arg(&format!("-o{}", opts.output_path.to_str().unwrap()))
        .status()
        .ok();
}
