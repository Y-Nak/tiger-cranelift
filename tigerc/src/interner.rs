use std::cell::RefCell;
use std::collections::HashMap;

use typed_arena::Arena;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Symbol(u32);

impl Symbol {
    pub fn intern(string: &str) -> Self {
        INTERNER.with(|interner| interner.borrow_mut().intern(string))
    }

    pub fn as_str(self) -> &'static str {
        INTERNER.with(|interner| interner.borrow().as_str(self))
    }

    pub fn is_kw(self) -> bool {
        (self.0 as usize) < PREFILL.len()
    }

    pub fn fresh(self) -> Self {
        INTERNER.with(|interner| interner.borrow_mut().fresh(self))
    }

    pub fn as_usize(self) -> usize {
        self.0 as usize
    }

    fn from_usize(n: usize) -> Self {
        Self(n as u32)
    }
}

struct Interner {
    strings: Arena<String>,
    string_refs: Vec<&'static str>,
    string_to_symbol: HashMap<&'static str, Symbol>,
    fresh_id: u32,
}

impl Interner {
    fn new() -> Self {
        Self {
            strings: Arena::new(),
            string_refs: Vec::new(),
            string_to_symbol: HashMap::new(),
            fresh_id: 0,
        }
    }

    fn prefill() -> Self {
        let mut interner = Self::new();
        for string in PREFILL {
            interner.intern(string);
        }
        interner
    }

    fn intern(&mut self, string: &str) -> Symbol {
        if let Some(&symbol) = self.string_to_symbol.get(string) {
            return symbol;
        }
        let string_ref = self.strings.alloc(string.to_string());
        let string_ref: &'static str = unsafe { &*(string_ref.as_str() as *const str) };
        let symbol = Symbol::from_usize(self.string_refs.len());
        self.string_refs.push(string_ref);
        self.string_to_symbol.insert(string_ref, symbol);
        symbol
    }

    fn as_str(&self, symbol: Symbol) -> &'static str {
        self.string_refs[symbol.as_usize()]
    }

    fn fresh(&mut self, symbol: Symbol) -> Symbol {
        let s = format!("{}#{}", self.as_str(symbol), self.fresh_id);
        self.fresh_id += 1;
        self.intern(&s)
    }
}

thread_local! {
    static INTERNER: RefCell<Interner> = RefCell::new( {
        Interner::prefill()
    });
}

macro_rules! decl_kw {
    ($(($ident:ident, $str:expr, $symbol_id:expr)),+)  => {
        #[allow(non_upper_case_globals)]
        pub mod kw {
            use super::*;
            $(pub const $ident: Symbol = Symbol($symbol_id);)+
        }
        const PREFILL:&[&'static str] = &[$($str),+];
    }
}

decl_kw! {
    (Array,    "array",    0),
    (Break,    "break",    1),
    (Do,       "do",       2),
    (Else,     "else",     3),
    (End,      "end",      4),
    (For,      "for",      5),
    (Function, "function", 6),
    (If,       "if",       7),
    (In,       "in",       8),
    (Let,      "let",      9),
    (Nil,      "nil",      10),
    (Of,       "of",       11),
    (Then,     "then",     12),
    (To,       "to",       13),
    (Type,     "type",     14),
    (Var,      "var",      15),
    (While,    "while",    16),
    (Main,     "main",     17)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern() {
        let s0_1 = Symbol::intern("s0");
        let s0_2 = Symbol::intern("s0");
        assert_eq!(s0_1, s0_2);

        let s1 = Symbol::intern("s1");
        assert_ne!(s0_1, s1);
    }

    #[test]
    fn test_back_to_string() {
        let symbol = Symbol::intern("Tiger");
        assert_eq!("Tiger", symbol.as_str());
    }

    #[test]
    fn test_kw() {
        let kw = "while";
        assert!(Symbol::intern(kw).is_kw());

        let not_kw = "Tiger";
        assert!(!Symbol::intern(not_kw).is_kw());
    }
}
