use crate::impl_prelude::*;
use crate::symbol_table::SymbolTable;

pub struct VEnv(SymbolTable<ValueEntry>);

impl VEnv {
    // TODO: Add  built-in function
    pub fn new() -> Self {
        Self(SymbolTable::new())
    }

    pub fn insert_func(
        &mut self,
        name: Symbol,
        args: Vec<TyKind>,
        ret_ty: TyKind,
        depth: u32,
    ) -> bool {
        let entry = ValueEntry {
            kind: ValueEntryKind::Func { args, ret_ty },
            depth,
        };
        self.insert(name, entry)
    }

    pub fn insert_var(&mut self, name: Symbol, ty: TyKind, depth: u32) -> bool {
        let entry = ValueEntry {
            kind: ValueEntryKind::Var { ty },
            depth,
        };
        self.insert(name, entry)
    }

    pub fn look_var(&mut self, name: Symbol) -> Option<(&TyKind, u32)> {
        match &self.0.look(name)? {
            ValueEntry {
                kind: ValueEntryKind::Var { ty },
                depth,
            } => Some((ty, *depth)),
            _ => None,
        }
    }

    pub fn look_func(&mut self, name: Symbol) -> Option<(&[TyKind], &TyKind, u32)> {
        match &self.0.look(name)? {
            ValueEntry {
                kind: ValueEntryKind::Func { args, ret_ty },
                depth,
            } => Some((args, ret_ty, *depth)),
            _ => None,
        }
    }

    pub fn enter_scope(&mut self) {
        self.0.enter_scope();
    }

    pub fn exit_scope(&mut self) {
        self.0.exit_scope();
    }

    fn insert(&mut self, name: Symbol, entry: ValueEntry) -> bool {
        if let Some(ValueEntry {
            depth: inserted_depth,
            ..
        }) = self.0.look(name)
        {
            if *inserted_depth != entry.depth {
                return false;
            }
        }

        self.0.insert(name, entry);
        true
    }
}

pub struct TEnv(SymbolTable<TyEntry>);

impl TEnv {
    pub fn new() -> Self {
        let mut tenv = Self(SymbolTable::new());

        tenv.insert(Symbol::intern("int"), TyKind::Int, 0);
        tenv.insert(Symbol::intern("string"), TyKind::String_, 0);
        tenv
    }
    pub fn enter_scope(&mut self) {
        self.0.enter_scope();
    }

    pub fn exit_scope(&mut self) {
        self.0.exit_scope()
    }

    pub fn look(&self, symbol: Symbol) -> Option<(&TyKind, u32)> {
        match self.0.look(symbol) {
            Some(TyEntry { ty, depth }) => Some((ty, *depth)),
            None => None,
        }
    }

    pub fn insert(&mut self, name: Symbol, ty: TyKind, depth: u32) -> bool {
        debug_assert!(!ty.is_alias());

        let entry = TyEntry { ty, depth };
        if let Some(TyEntry {
            depth: inserted_depth,
            ..
        }) = self.0.look(name)
        {
            if *inserted_depth == entry.depth {
                return false;
            }
        }

        self.0.insert(name, entry);
        true
    }
}

struct ValueEntry {
    kind: ValueEntryKind,
    depth: u32,
}

enum ValueEntryKind {
    Func { args: Vec<TyKind>, ret_ty: TyKind },
    Var { ty: TyKind },
}

struct TyEntry {
    ty: TyKind,
    depth: u32,
}
