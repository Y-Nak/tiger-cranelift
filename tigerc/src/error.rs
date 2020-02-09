use std::borrow::Cow;

use colored::*;

use crate::impl_prelude::*;

#[derive(Debug)]
pub struct Error {
    msg: Cow<'static, str>,
    pos: Pos,
}

impl Error {
    pub fn new(msg: Cow<'static, str>, pos: Pos) -> Self {
        Self { msg, pos }
    }

    pub fn eprint(&self, code: &[u8], file_name: &str) {
        eprintln!("{}: {}", "Error".red().bold(), self.msg.bold());
        eprintln!(
            "{}:l{}-l{}",
            file_name, self.pos.start.line, self.pos.end.line
        );
        eprintln!("{}", self.code_at(self.pos, code));
    }

    fn code_at<'a>(&self, pos: Pos, code: &'a [u8]) -> &'a str {
        unsafe { std::str::from_utf8_unchecked(&code[pos.start.byte_pos..pos.end.byte_pos]) }
    }
}
