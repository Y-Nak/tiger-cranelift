use std::ops;

pub type BytePos = usize;

#[derive(PartialOrd, Ord, PartialEq, Eq, Clone, Copy, Debug)]
pub struct Cursor {
    pub byte_pos: BytePos,
    pub line: u32,
}

impl Cursor {
    pub fn new(byte_pos: BytePos, line: u32) -> Self {
        Self { byte_pos, line }
    }

    pub fn proceed_byte(self, proceed: BytePos) -> Self {
        Self::new(self.byte_pos + proceed, self.line)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pos {
    pub start: Cursor,
    pub end: Cursor,
}

impl Pos {
    pub fn new(start: Cursor, end: Cursor) -> Self {
        Self { start, end }
    }

    pub fn from_cursor(start: Cursor) -> Self {
        Self {
            start,
            end: start.proceed_byte(1),
        }
    }
}

impl ops::Add for Pos {
    type Output = Pos;
    fn add(self, rhs: Self) -> Pos {
        let start = if self.start < rhs.start {
            self.start
        } else {
            rhs.start
        };

        let end = if self.end < rhs.end {
            rhs.end
        } else {
            self.end
        };

        Self::new(start, end)
    }
}
