pub mod ast;
pub mod error;
pub mod intern;
pub mod lexer;
pub mod parser;
pub mod pos;
pub mod ty;

pub type Result<T> = std::result::Result<T, error::Error>;

mod impl_prelude {
    use super::*;

    pub use super::Result;
    pub use error::Error;
    pub use intern::{kw, Symbol};
    pub use pos::{BytePos, Cursor, Pos};
}
