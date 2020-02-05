use std::borrow::Cow;

use colored::*;

use crate::impl_prelude::*;

#[derive(Debug)]
pub struct Error {
    msg: Cow<'static, str>,
    pos: Pos,
    sub_descs: Vec<(Cow<'static, str>, Pos)>,
}

impl Error {
    pub fn new(msg: Cow<'static, str>, pos: Pos) -> Self {
        Self {
            msg,
            pos,
            sub_descs: vec![],
        }
    }

    pub fn append_sub_desc(&mut self, msg: Cow<'static, str>, pos: Pos) {
        self.sub_descs.push((msg, pos))
    }

    pub fn eprint(&mut self, code: &[u8], file_name: &str) {
        eprintln!("{}: {}", "Error".red().bold(), self.msg.bold());
        eprintln!("{}:{}", file_name, self.pos.start.line,);
        eprintln!("{}", self.code_at(self.pos, code));

        self.sub_descs
            .sort_by(|a, b| a.1.start.line.cmp(&b.1.start.line));

        for (msg, pos) in self.sub_descs.iter() {
            eprintln!("{}: {}", "Cause".blue().bold(), msg.bold());
            eprintln!("{}\n", self.code_at(*pos, code));
        }
    }

    fn code_at<'a>(&self, pos: Pos, code: &'a [u8]) -> &'a str {
        unsafe { std::str::from_utf8_unchecked(&code[pos.start.byte_pos..pos.end.byte_pos]) }
    }
}
