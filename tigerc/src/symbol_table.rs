use std::collections::HashMap;

use crate::impl_prelude::*;

pub struct SymbolTable<T> {
    table: HashMap<Symbol, Vec<T>>,
    symbols: Vec<Vec<Symbol>>,
}

impl<T> SymbolTable<T> {
    pub fn new() -> Self {
        Self {
            table: HashMap::new(),
            symbols: Vec::new(),
        }
    }

    pub fn enter_scope(&mut self) {
        self.symbols.push(vec![]);
    }

    pub fn exit_scope(&mut self) {
        for sym in self.symbols.pop().unwrap() {
            self.table.get_mut(&sym).unwrap().pop().unwrap();
        }
    }

    pub fn insert(&mut self, sym: Symbol, value: T) {
        self.table.entry(sym).or_default().push(value)
    }

    pub fn look(&self, sym: Symbol) -> Option<&T> {
        match self.table.get(&sym) {
            Some(v) => v.last(),
            None => None,
        }
    }
}

impl<T> Default for SymbolTable<T> {
    fn default() -> Self {
        Self::new()
    }
}
