use crate::impl_prelude::*;

#[derive(Clone)]
pub struct Ty {
    pub kind: TyKind,
    pub pos: Pos,
}

impl Ty {
    pub fn new(kind: TyKind, pos: Pos) -> Self {
        Self { kind, pos }
    }
}

#[derive(Clone)]
pub enum TyKind {
    Int,
    Unit,
    Nil,
    Alias(Symbol),
    Array(Box<Ty>),
    Record(Vec<(Symbol, Ty)>),
    Invalid,
}

impl TyKind {
    pub fn is_complete(&self) -> bool {
        use TyKind::*;
        match self {
            Int | Unit | Nil => true,
            Alias(_) | Invalid => false,
            Array(ty) => ty.kind.is_complete(),
            Record(field) => {
                for (_, t) in field.iter() {
                    if !t.kind.is_complete() {
                        return false;
                    }
                }
                true
            }
        }
    }
}
