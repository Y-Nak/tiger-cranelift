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

#[derive(PartialEq, Eq, Clone)]
pub enum TyKind {
    Int,
    Unit,
    String_,
    Nil,
    Alias(Symbol),
    Array {
        elem_ty: Box<TyKind>,
        unique: u32,
    },
    Record {
        field: Vec<(Symbol, TyKind)>,
        unique: u32,
    },
    Invalid,
}

impl TyKind {
    pub fn is_complete(&self) -> bool {
        use TyKind::*;
        match self {
            Int | Unit | Nil | String_ => true,
            Alias(_) | Invalid => false,
            Array { elem_ty, .. } => elem_ty.is_complete(),
            Record { field, .. } => {
                for (_, t) in field.iter() {
                    if !t.is_complete() {
                        return false;
                    }
                }
                true
            }
        }
    }
}
