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

    pub fn dummy() -> Self {
        Self::new(0, 0)
    }

    pub fn is_dummy(self) -> bool {
        self.byte_pos == 0 && self.line == 0
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

    pub fn dummy() -> Self {
        Self::new(Cursor::dummy(), Cursor::dummy())
    }

    pub fn from_cursor(start: Cursor) -> Self {
        Self {
            start,
            end: start.proceed_byte(1),
        }
    }

    pub fn is_dummy(self) -> bool {
        self.start.is_dummy() || self.end.is_dummy()
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

impl ops::AddAssign for Pos {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
