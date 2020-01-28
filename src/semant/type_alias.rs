// TODO: Insert correct position to handle error properly.

use std::collections::{HashMap, HashSet};

use super::env::TEnv;
use crate::impl_prelude::*;

use MayBeResolved::*;

pub struct AliasResolver<'a> {
    env: &'a TEnv,
    work_list: Vec<Symbol>,
    resolves: HashMap<Symbol, MayBeResolved>,
}

impl<'a> AliasResolver<'a> {
    pub fn new(env: &'a TEnv) -> Self {
        Self {
            env,
            work_list: Vec::new(),
            resolves: HashMap::new(),
        }
    }

    pub fn add_to_worklist(&mut self, symbol: Symbol, ty: &TyKind) -> bool {
        let maybe_resolved = as_maybe_resolved(ty);
        if maybe_resolved.has_resolved() {
            self.resolves.insert(symbol, maybe_resolved).is_none()
        } else {
            self.work_list.push(symbol);
            self.resolves.insert(symbol, maybe_resolved).is_none()
        }
    }

    pub fn resolve(mut self) -> Result<HashMap<Symbol, TyKind>> {
        let mut visited = HashSet::new();
        for i in 0..self.work_list.len() {
            self.try_resolve(self.work_list[i], &mut visited)?;
            debug_assert!(visited.len() == 0);
        }

        Ok(self
            .resolves
            .into_iter()
            .map(|(k, v)| (k, v.resolve().unwrap()))
            .collect())
    }

    fn try_resolve(&mut self, ty_name: Symbol, visited: &mut HashSet<Symbol>) -> Result<TyKind> {
        match self.resolves.get(&ty_name).unwrap() {
            Resolved(kind) => Ok(kind.clone()),
            &UnResolved(next_ty) => {
                visited.insert(ty_name);
                if visited.contains(&next_ty) {
                    return Err(Error::new("Cycle definition found".into(), Pos::dummy()));
                }

                let kind = if self.resolves.get(&next_ty).is_some() {
                    // Try resolve type alias in same depth
                    let result = self.try_resolve(next_ty, visited)?;
                    self.resolves.insert(ty_name, Resolved(result.clone()));
                    result
                } else if let Some((ty, _)) = self.env.look(next_ty) {
                    // Try find type alias in shallow depth.
                    self.resolves.insert(next_ty, Resolved(ty.clone()));
                    ty.clone()
                } else {
                    return Err(Error::new("Undefind type alias".into(), Pos::dummy()));
                };

                visited.remove(&ty_name);
                Ok(kind)
            }
        }
    }
}

enum MayBeResolved {
    Resolved(TyKind),
    UnResolved(Symbol),
}

impl MayBeResolved {
    fn has_resolved(&self) -> bool {
        match self {
            Resolved(..) => true,
            UnResolved(..) => false,
        }
    }

    fn resolve(self) -> Option<TyKind> {
        match self {
            Resolved(inner) => Some(inner),
            _ => None,
        }
    }
}

fn as_maybe_resolved(ty: &TyKind) -> MayBeResolved {
    match ty {
        TyKind::Alias(symbol) => UnResolved(*symbol),
        _ => Resolved(ty.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alias_ty(s: &str) -> TyKind {
        TyKind::Alias(Symbol::intern(s))
    }

    fn alias_name(ty: &TyKind) -> Symbol {
        match ty {
            TyKind::Alias(symbol) => *symbol,
            _ => panic!(),
        }
    }

    fn make_record(field: Vec<(&str, &str)>, unique: u32) -> TyKind {
        let field = field
            .into_iter()
            .map(|(name, ty_ref)| (Symbol::intern(name), alias_ty(ty_ref)))
            .collect();
        TyKind::Record { field, unique }
    }

    #[test]
    fn test_simple_alias() {
        let tenv = TEnv::new();
        let mut resolver = AliasResolver::new(&tenv);
        // type a = int;
        // type b = a;
        // type c = b;
        let type_defs = vec![("a", "int"), ("b", "a"), ("c", "b")];
        for (lhs, rhs) in type_defs.iter() {
            resolver.add_to_worklist(Symbol::intern(lhs), &alias_ty(rhs));
        }

        let resolved = resolver.resolve().unwrap();

        for (name, _) in type_defs.iter() {
            let name = Symbol::intern(name);
            assert_eq!(resolved.get(&name).unwrap(), &TyKind::Int);
        }
    }

    #[test]
    fn test_cycle_def() {
        let tenv = TEnv::new();
        let mut resolver = AliasResolver::new(&tenv);
        // type a = int;
        // type b = a;
        // type c = b;
        let type_defs = vec![("a", "b"), ("b", "a"), ("c", "b")];
        for (lhs, rhs) in type_defs.iter() {
            resolver.add_to_worklist(Symbol::intern(lhs), &alias_ty(rhs));
        }

        assert!(resolver.resolve().is_err());
    }

    #[test]
    fn test_rec_type() {
        let mut tenv = TEnv::new();
        let mut resolver = AliasResolver::new(&tenv);
        // type list = {head: int, tail: list}
        let type_name = Symbol::intern("list");
        let list_type = make_record(vec![("head", "int"), ("tail", "list")], 0);

        resolver.add_to_worklist(type_name, &list_type);
        for (name, ty_kind) in resolver.resolve().unwrap().into_iter() {
            tenv.insert(name, ty_kind, 0);
        }

        let resolved_list = tenv.look(type_name).unwrap().0;

        match resolved_list {
            TyKind::Record { field, .. } => {
                assert_eq!(field[0].0, Symbol::intern("head"));
                assert_eq!(field[1].0, Symbol::intern("tail"));

                let head_type_alias = alias_name(&field[0].1);
                assert_eq!(tenv.look(head_type_alias).unwrap().0, &TyKind::Int);

                let tail_type_alias = alias_name(&field[1].1);
                assert_eq!(tenv.look(tail_type_alias).unwrap().0, resolved_list);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_mutual_rec_type() {
        let mut tenv = TEnv::new();
        let mut resolver = AliasResolver::new(&tenv);
        // type tree = {key: int, children: treelist}
        // type treelist = {hd: tree, tree: treelist}
        let tree_type_name = Symbol::intern("tree");
        let treelist_type_name = Symbol::intern("treelist");

        let tree_type = make_record(vec![("key", "int"), ("children", "treelist")], 0);
        let treelist_type = make_record(vec![("hd", "tree"), ("tl", "treelist")], 0);

        for (name, ty_kind) in vec![
            (tree_type_name, &tree_type),
            (treelist_type_name, &treelist_type),
        ]
        .iter()
        {
            resolver.add_to_worklist(*name, ty_kind);
        }

        for (name, ty_kind) in resolver.resolve().unwrap().into_iter() {
            tenv.insert(name, ty_kind, 0);
        }

        let resolved_tree_type = tenv.look(tree_type_name).unwrap().0;
        match resolved_tree_type {
            TyKind::Record { field, .. } => {
                let children_type_alias = alias_name(&field[1].1);
                assert_eq!(tenv.look(children_type_alias).unwrap().0, &treelist_type);
            }
            _ => panic!(),
        }

        let resolved_treelist_type = tenv.look(treelist_type_name).unwrap().0;
        match resolved_treelist_type {
            TyKind::Record { field, .. } => {
                let hd_type_alias = alias_name(&field[0].1);
                assert_eq!(tenv.look(hd_type_alias).unwrap().0, &tree_type);
            }
            _ => panic!(),
        }
    }
}
