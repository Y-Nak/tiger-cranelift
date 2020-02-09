use crate::ast::{ExprKind::*, *};
use crate::impl_prelude::*;
use crate::symbol_table::SymbolTable;

pub struct LambdaLifter {
    func_env: FuncEnv,
    functions: Vec<Function>,
}

impl LambdaLifter {
    pub fn new() -> Self {
        Self {
            func_env: FuncEnv::new(),
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

                // Liftup functions in declaration.
                self.mangle_decls(decls);
                self.liftup_decls(decls);

                // Liftup functions in expression.
                self.liftup_func_in_expr(body);

                self.func_env.exit_scope();
            }

            UnOp { lhs, .. } | FieldAccess { lvalue: lhs, .. } => self.liftup_func_in_expr(lhs),

            BinOp { lhs, rhs, .. }
            | Assign { lvalue: lhs, rhs }
            | Index {
                lvalue: lhs,
                index: rhs,
            }
            | While {
                cond: lhs,
                body: rhs,
            }
            | Array {
                size: lhs,
                init: rhs,
                ..
            } => {
                self.liftup_func_in_expr(lhs);
                self.liftup_func_in_expr(rhs);
            }

            If { cond, then, else_ } => {
                self.liftup_func_in_expr(cond);
                self.liftup_func_in_expr(then);
                if let Some(else_) = else_ {
                    self.liftup_func_in_expr(else_);
                }
            }

            For { from, to, body, .. } => {
                self.liftup_func_in_expr(from);
                self.liftup_func_in_expr(to);
                self.liftup_func_in_expr(body);
            }

            Record { fields, .. } => fields
                .iter_mut()
                .for_each(|(_, field)| self.liftup_func_in_expr(field)),

            ExprSeq(exprs) => exprs
                .iter_mut()
                .for_each(|expr| self.liftup_func_in_expr(expr)),

            Call { name, args } => self.recompute_callsite(name, args),

            Break | Var(_) | Lit(_) => {}
        }
    }

    fn mangle_decls(&mut self, decls: &mut [Decl]) {
        for decl in decls.iter_mut() {
            self.mangle_decl(decl);
        }
    }

    fn liftup_decls(&mut self, decls: &mut Vec<Decl>) {
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
    }

    /// 1. Mangle function name, then copy free variables to their args.
    /// 2. Register mangled function to env.
    fn mangle_decl(&mut self, decl: &mut Decl) {
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

    fn recompute_callsite(&mut self, name: &mut Symbol, args: &mut Vec<Expr>) {
        for arg in args.iter_mut() {
            self.liftup_func_in_expr(arg);
        }
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

struct FuncEnv(SymbolTable<MangledFunctionDecl>);

impl FuncEnv {
    pub fn new() -> Self {
        let mut env = FuncEnv(SymbolTable::new());
        env.prefill_builtin_functions();
        env
    }

    fn prefill_builtin_functions(&mut self) {
        self.prefill_func("print");
        self.prefill_func("println");
        self.prefill_func("print_int");
        self.prefill_func("flush");
        self.prefill_func("getchar");
        self.prefill_func("ord");
        self.prefill_func("chr");
        self.prefill_func("substring");
        self.prefill_func("concat");
        self.prefill_func("size");
        self.prefill_func("not");
        self.prefill_func("exit");
    }

    fn prefill_func(&mut self, name: &str) {
        let name = Symbol::intern(name);
        let mangled_print = MangledFunctionDecl {
            name,
            free_variables: Vec::new(),
        };

        self.insert(name, mangled_print);
    }
}

impl std::ops::Deref for FuncEnv {
    type Target = SymbolTable<MangledFunctionDecl>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for FuncEnv {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
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
