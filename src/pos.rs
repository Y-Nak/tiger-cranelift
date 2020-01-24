use std::ops;

pub type BytePos = usize;

#[derive(PartialOrd, Ord, PartialEq, Eq, Clone, Copy)]
pub struct Cursor {
    pub byte_pos: BytePos,
    pub line: u32,
}

impl Cursor {
    pub fn new(byte_pos: BytePos, line: u32) -> Self {
        Self { byte_pos, line }
    }
}

#[derive(Clone, Copy)]
pub struct Pos {
    pub start: Cursor,
    pub end: Cursor,
}

impl Pos {
    pub fn new(start: Cursor, end: Cursor) -> Self {
        Self { start, end }
    }

    pub fn line_range(self) -> ops::Range<u32> {
        (self.start.line..self.end.line + 1)
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
