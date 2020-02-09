use crate::impl_prelude::*;

pub struct FuncContext {
    depth: u32,
    free_variables: Vec<(Symbol, TyKind)>,
}

impl FuncContext {
    pub fn new(depth: u32) -> Self {
        Self {
            depth,
            free_variables: Vec::new(),
        }
    }

    pub fn maybe_push_free_var(&mut self, var: (Symbol, &TyKind, u32)) -> bool {
        let (symbol, ty, depth) = var;
        if self.depth > depth && !self.contains(symbol) {
            self.free_variables.push((symbol, ty.clone()));
            true
        } else {
            false
        }
    }

    pub fn free_variables(&mut self) -> Vec<(Symbol, TyKind)> {
        let mut vars = Vec::new();
        std::mem::swap(&mut self.free_variables, &mut vars);
        vars
    }

    fn contains(&self, symbol: Symbol) -> bool {
        self.free_variables
            .iter()
            .find(|(name, _)| *name == symbol)
            .is_some()
    }
}
