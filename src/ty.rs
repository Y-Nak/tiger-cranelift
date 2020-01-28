use crate::impl_prelude::*;
use TyKind::*;

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

#[derive(Clone, Debug)]
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
        match self {
            Int | Unit | Nil | String_ | Array { .. } | Record { .. } => true,
            Alias(_) | Invalid => false,
        }
    }

    pub fn is_record(&self) -> bool {
        match self {
            Record { .. } => true,
            _ => false,
        }
    }

    pub fn is_array(&self) -> bool {
        match self {
            Array { .. } => true,
            _ => false,
        }
    }

    pub fn is_alias(&self) -> bool {
        match self {
            Alias(..) => true,
            _ => false,
        }
    }

    pub fn record_field_unchecked(&self) -> &[(Symbol, TyKind)] {
        match self {
            TyKind::Record { field, .. } => &field,
            _ => panic!("Expected record type"),
        }
    }

    pub fn array_elem_unchecked(&self) -> &TyKind {
        match self {
            TyKind::Array { elem_ty, .. } => elem_ty,
            _ => panic!("Expectd array type"),
        }
    }
}

impl PartialEq for TyKind {
    fn eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (TyKind::Int, TyKind::Int)
            | (TyKind::String_, TyKind::String_)
            | (TyKind::Nil, TyKind::Nil) => true,

            (TyKind::Alias(lhs), TyKind::Alias(rhs)) => lhs == rhs,

            (TyKind::Array { unique: lhs, .. }, TyKind::Array { unique: rhs, .. })
            | (TyKind::Record { unique: lhs, .. }, TyKind::Record { unique: rhs, .. }) => {
                lhs == rhs
            }

            _ => false,
        }
    }
}
