pub mod ast;
pub mod codegen;
pub mod error;
pub mod interner;
pub mod lexer;
pub mod parser;
pub mod pos;
pub mod semant;
pub mod ty;

mod symbol_table;

pub type Result<T> = std::result::Result<T, error::Error>;

mod impl_prelude {
    use super::*;

    pub use super::Result;
    pub use error::Error;
    pub use interner::{kw, Symbol};
    pub use pos::{BytePos, Cursor, Pos};
    pub use ty::{Ty, TyKind};
}

pub mod prelude {
    pub use codegen::CodeGen;
    pub use parser::Parser;
    pub use semant::{LambdaLifter, SemanticAnalyzer};

    use super::*;
    use std::path::PathBuf;

    #[derive(Clone)]
    pub struct Opts {
        pub output_path: PathBuf,
        pub dump_clif: bool,
        pub opt_level: String,
    }
}
