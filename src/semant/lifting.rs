use crate::ast::{ExprKind::*, *};
use crate::impl_prelude::*;
use crate::symbol_table::SymbolTable;

pub struct LambdaLifter {
    func_env: SymbolTable<MangledFunctionDecl>,
    functions: Vec<Function>,
}

impl LambdaLifter {
    pub fn new() -> Self {
        Self {
            func_env: SymbolTable::new(),
            functions: Vec::new(),
        }
    }

    pub fn lift_functions(mut self, expr: Expr) -> Vec<Function> {
        let mut main_func = fold_into_main(expr);

        self.liftup_func_in_expr(&mut main_func.body);
        self.functions.push(main_func);

        self.functions
    }

    fn liftup_func_in_expr(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            Let { decls, body } => {
                self.func_env.enter_scope();

                // 1. Mangle function name, then copy free variables to their args.
                // 2. Register mangled function to env.
                for decl in decls.iter_mut() {
                    if let DeclKind::Function(func) = &mut decl.kind {
                        let mangled_name = func.name.fresh();
                        let mangled_decl = MangledFunctionDecl {
                            name: mangled_name,
                            free_variables: func
                                .free_variables
                                .iter()
                                .map(|(arg_name, _)| *arg_name)
                                .collect(),
                        };
                        self.func_env.insert(func.name, mangled_decl);
                        recompute_func_decl(func, mangled_name);
                    }
                }

                // Make function global.
                let mut i = 0;
                while i < decls.len() {
                    if decls[i].is_func() {
                        let mut func = decls.remove(i).extract_func_unchecked();
                        self.liftup_func_in_expr(&mut func.body);
                        self.functions.push(func);
                    } else {
                        i += 1;
                    }
                }

                self.liftup_func_in_expr(body);

                self.func_env.exit_scope();
            }
            Call { name, args } => self.recompute_callsite(name, args),
            BinOp { lhs, rhs, .. } => {
                self.liftup_func_in_expr(lhs);
                self.liftup_func_in_expr(rhs);
            }
            UnOp { lhs, .. } => self.liftup_func_in_expr(lhs),
            Record { fields, .. } => fields
                .iter_mut()
                .for_each(|(_, field)| self.liftup_func_in_expr(field)),
            Array { size, init, .. } => {
                self.liftup_func_in_expr(size);
                self.liftup_func_in_expr(init);
            }
            If { cond, then, else_ } => {
                self.liftup_func_in_expr(cond);
                self.liftup_func_in_expr(then);
                if let Some(else_) = else_ {
                    self.liftup_func_in_expr(else_);
                }
            }
            While { cond, body } => {
                self.liftup_func_in_expr(cond);
                self.liftup_func_in_expr(body);
            }
            For { from, to, body, .. } => {
                self.liftup_func_in_expr(from);
                self.liftup_func_in_expr(to);
                self.liftup_func_in_expr(body);
            }
            ExprSeq(exprs) => exprs
                .iter_mut()
                .for_each(|expr| self.liftup_func_in_expr(expr)),

            FieldAccess { lvalue, .. } => self.liftup_func_in_expr(lvalue),
            Index { lvalue, index } => {
                self.liftup_func_in_expr(lvalue);
                self.liftup_func_in_expr(index);
            }
            Assign { lvalue, rhs } => {
                self.liftup_func_in_expr(lvalue);
                self.liftup_func_in_expr(rhs)
            }

            Break | Var(_) | Lit(_) => {}
        }
    }

    fn recompute_callsite(&self, name: &mut Symbol, args: &mut Vec<Expr>) {
        let mangled_dec = self.func_env.look(*name).unwrap();
        *name = mangled_dec.name;
        for free_var in mangled_dec.free_variables.iter() {
            let expr = Expr::new(Var(*free_var), Pos::dummy());
            args.push(expr);
        }
    }
}

impl Default for LambdaLifter {
    fn default() -> Self {
        Self::new()
    }
}

struct MangledFunctionDecl {
    name: Symbol,
    free_variables: Vec<Symbol>,
}

fn fold_into_main(expr: Expr) -> Function {
    let name = Symbol::intern("main");
    if expr.ty.kind == TyKind::Int {
        Function::new(name, Vec::new(), expr.ty.clone(), expr)
    } else {
        let mut expr_seq = vec![expr];
        expr_seq.push(Expr::new(
            Lit(LitKind::Num(Symbol::intern("0"))),
            Pos::dummy(),
        ));
        let body = Expr::new(ExprSeq(expr_seq), Pos::dummy());
        Function::new(name, Vec::new(), Ty::new(TyKind::Int, Pos::dummy()), body)
    }
}

fn recompute_func_decl(func: &mut Function, mangled_name: Symbol) {
    func.name = mangled_name;
    for (name, ty) in func.free_variables.iter() {
        func.args.push((*name, Ty::new(ty.clone(), Pos::dummy())));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;
    use crate::semant::SemanticAnalyzer;

    fn analyze(code: &str) -> Expr {
        let mut parser = Parser::new(code.as_bytes()).unwrap();
        let mut expr = parser.parse().unwrap();

        let mut semantic_analyzer = SemanticAnalyzer::new();
        semantic_analyzer.analyze_expr(&mut expr).unwrap();
        expr
    }

    #[test]
    fn test_lifting() {
        let code = "
            let
                var n := 10
                function inner(a: int) : int =
                    a + n
            in
                inner(10)
            end
            ";

        let expr = analyze(code);

        let lifter = LambdaLifter::new();
        let mut functions = lifter.lift_functions(expr);

        assert_eq!(functions.len(), 2);

        let inner_func = functions.remove(0);
        assert_eq!(inner_func.free_variables.len(), 1);
        assert_eq!(inner_func.args.len(), 2);

        let mut main_func = functions.remove(0);
        assert_eq!(main_func.name.as_str(), "main");

        match &mut main_func.body.kind {
            Let { body, decls } => {
                assert_eq!(decls.len(), 1);
                match &mut body.kind {
                    ExprSeq(exprs) => match exprs.remove(0).kind {
                        Call { name, args } => {
                            assert_eq!(name, inner_func.name);
                            assert_eq!(args.len(), 2);
                        }
                        _ => panic!(),
                    },
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }
}
