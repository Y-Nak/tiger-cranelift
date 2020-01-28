use crate::ast::*;
use crate::impl_prelude::*;

use super::env::{TEnv, VEnv};
use super::{func_context::FuncContext, type_alias::AliasResolver};

pub struct SemanticAnalyzer {
    venv: VEnv,
    tenv: TEnv,
    depth: u32,
    loop_depth: u32,
    func_context: FuncContext,
}

impl SemanticAnalyzer {
    pub fn new() -> Self {
        Self {
            venv: VEnv::new(),
            tenv: TEnv::new(),
            depth: 0,
            loop_depth: 0,
            func_context: FuncContext::new(0),
        }
    }

    pub fn analyze_expr(&mut self, expr: &mut Expr) -> Result<()> {
        let kind = match &mut expr.kind {
            ExprKind::BinOp { kind, lhs, rhs } => self.analyze_binop(kind, lhs, rhs)?,
            ExprKind::UnOp {
                kind: UnOpKind::Minus,
                lhs,
            } => {
                self.analyze_expr(lhs)?;
                self.expect_int(lhs)?;
                TyKind::Int
            }
            ExprKind::Lit(lit) => self.analyze_literal(lit)?,
            ExprKind::Call { name, args } => self.analyze_call(*name, args, expr.pos)?,
            ExprKind::Record { fields, ty } => self.analyze_record(fields, &ty, expr.pos)?,
            ExprKind::Array {
                size,
                init,
                elem_ty,
            } => self.analyze_array(size, init, &elem_ty)?,
            ExprKind::If { cond, then, else_ } => {
                self.analyze_if(cond, then, else_.as_deref_mut())?
            }
            ExprKind::While { cond, body } => self.analyze_while(cond, body)?,
            ExprKind::For {
                var,
                from,
                to,
                body,
            } => self.analyze_for(*var, from, to, body)?,
            ExprKind::Let { decls, body } => self.analyze_let(decls, body)?,
            ExprKind::Break => {
                if self.loop_depth > 0 {
                    TyKind::Unit
                } else {
                    return Err(Error::new("Break not in loop".into(), expr.pos));
                }
            }
            ExprKind::ExprSeq(exprs) => self.analyze_expr_seq(exprs)?,
            ExprKind::Var(name) => self.analyze_var(*name, expr.pos)?,

            ExprKind::FieldAccess { lvalue, field } => {
                self.analyze_field_access(lvalue, *field, expr.pos)?
            }
            ExprKind::Index { lvalue, index } => self.analyze_indexing(lvalue, index, expr.pos)?,
            ExprKind::Assign { lvalue, rhs } => self.analyze_assign(lvalue, rhs, expr.pos)?,
        };
        expr.ty = Ty::new(self.resolve_alias(&kind, Pos::dummy())?, Pos::dummy());

        Ok(())
    }

    fn analyze_decls(&mut self, decls: &mut [Decl]) -> Result<()> {
        // Resolve type alias.
        self.resolve_type_alias(decls)?;

        // Analyze variable declaration.
        for decl in decls.iter_mut() {
            match &mut decl.kind {
                DeclKind::VarDec(var_dec) => self.analyze_var_dec(var_dec)?,
                _ => continue,
            }
        }

        // Analyze function declaration.
        for decl in decls.iter_mut() {
            match &mut decl.kind {
                DeclKind::Function(f) => self.analyze_func(f)?,
                _ => continue,
            }
        }

        Ok(())
    }

    fn analyze_var_dec(&mut self, var_dec: &mut VarDec) -> Result<()> {
        self.analyze_expr(&mut var_dec.init)?;
        if var_dec.ty.is_some() {
            todo!();
        } else {
            if var_dec.init.ty.kind == TyKind::Nil {
                return Err(Error::new(
                    "Don't use nil without type annotation".into(),
                    var_dec.init.pos,
                ));
            }
            self.venv
                .insert_var(var_dec.name, var_dec.init.ty.kind.clone(), self.depth);
            var_dec.ty = Some(var_dec.init.ty.clone());
        }
        Ok(())
    }

    fn analyze_func(&mut self, f: &mut Function) -> Result<()> {
        self.venv.insert_func(
            f.name,
            f.args.iter().map(|arg| arg.1.kind.clone()).collect(),
            f.ret_ty.kind.clone(),
            self.depth,
        );
        self.enter_scope();
        self.func_context = FuncContext::new(self.depth);
        self.analyze_expr(&mut f.body)?;
        self.exit_scope();

        f.free_variables = self.func_context.free_variables();
        Ok(())
    }

    fn analyze_binop(
        &mut self,
        kind: &BinOpKind,
        lhs: &mut Expr,
        rhs: &mut Expr,
    ) -> Result<TyKind> {
        use BinOpKind::*;
        self.analyze_expr(lhs)?;
        self.analyze_expr(rhs)?;

        let result_ty = match kind {
            Add | Sub | Mul | Div | Lt | Le | Gt | Ge | LogicalAnd | LogicalOr => {
                self.expect_int(lhs)?;
                self.expect_int(rhs)?;
                TyKind::Int
            }
            Eq_ | Ne => self.try_type_promotion(&lhs.ty.kind, &rhs.ty.kind, lhs.pos + rhs.pos)?,
        };

        Ok(result_ty)
    }

    fn analyze_literal(&self, lit: &LitKind) -> Result<TyKind> {
        let ty_kind = match lit {
            LitKind::LitStr(..) => TyKind::String_,
            LitKind::Num(_) => TyKind::Int, // TODO: Check maximum integer value;
            LitKind::Nil => TyKind::Nil,
        };
        Ok(ty_kind)
    }

    fn analyze_call(&mut self, name: Symbol, args: &mut [Expr], pos: Pos) -> Result<TyKind> {
        for arg in args.iter_mut() {
            self.analyze_expr(arg)?;
        }

        let (arg_tys, ret_ty, _) = self
            .venv
            .look_func(name)
            .ok_or_else(|| Error::new("Undefined function".into(), pos))?;

        if args.len() != arg_tys.len() {
            return Err(Error::new("Inconsistent arity".into(), pos));
        }

        for (arg_ty, arg) in arg_tys.iter().zip(args) {
            if arg_ty != &arg.ty.kind {
                return Err(Error::new("Inconsistent type".into(), arg.pos));
            }
        }

        Ok(ret_ty.clone())
    }

    fn analyze_record(
        &mut self,
        fields: &mut [(Symbol, Expr)],
        ty: &Ty,
        pos: Pos,
    ) -> Result<TyKind> {
        let resolved_ty = self.resolve_alias(&ty.kind, ty.pos)?;
        if !resolved_ty.is_record() {
            return Err(Error::new("Expected record type".into(), ty.pos));
        }

        let ty_fields = resolved_ty.record_field_unchecked();
        if ty_fields.len() != fields.len() {
            return Err(Error::new("Inconsistent type".into(), pos));
        }

        for (init_expr, ty_field) in fields.iter_mut().zip(ty_fields) {
            let (symbol, expr) = init_expr;
            self.analyze_expr(expr)?;
            let (expected_symbol, expected_ty) = ty_field;
            if symbol != expected_symbol {
                return Err(Error::new("Unexpected field name".into(), expr.pos));
            }

            self.try_type_promotion(
                &expr.ty.kind,
                &self.resolve_alias(expected_ty, expr.pos)?,
                expr.pos,
            )?;
        }

        Ok(resolved_ty)
    }

    fn analyze_array(&mut self, size: &mut Expr, init: &mut Expr, ty: &Ty) -> Result<TyKind> {
        self.analyze_expr(size)?;
        self.expect_int(size)?;

        self.analyze_expr(init)?;
        let resolved_ty = self.resolve_alias(&ty.kind, ty.pos)?;
        if !resolved_ty.is_array() {
            return Err(self.type_error(ty.pos));
        }

        let result_ty = self.try_type_promotion(
            &init.ty.kind,
            &self.resolve_alias(resolved_ty.array_elem_unchecked(), ty.pos)?,
            init.ty.pos,
        )?;

        Ok(result_ty)
    }

    fn analyze_if(
        &mut self,
        cond: &mut Expr,
        then: &mut Expr,
        else_: Option<&mut Expr>,
    ) -> Result<TyKind> {
        self.analyze_expr(cond)?;
        self.expect_int(cond)?;

        self.analyze_expr(then)?;

        if let Some(else_) = else_ {
            self.analyze_expr(else_)?;
            if then.ty.kind != else_.ty.kind {
                return Err(self.type_error(else_.pos));
            }
        }

        Ok(then.ty.kind.clone())
    }

    fn analyze_while(&mut self, cond: &mut Expr, body: &mut Expr) -> Result<TyKind> {
        self.analyze_expr(cond)?;
        self.expect_int(cond)?;

        self.loop_depth += 1;
        self.analyze_expr(body)?;
        self.loop_depth -= 1;

        Ok(body.ty.kind.clone())
    }

    fn analyze_for(
        &mut self,
        var: Symbol,
        from: &mut Expr,
        to: &mut Expr,
        body: &mut Expr,
    ) -> Result<TyKind> {
        self.analyze_expr(from)?;
        self.expect_int(from)?;

        self.analyze_expr(to)?;
        self.expect_int(to)?;

        self.enter_scope();
        self.venv.insert_var(var, TyKind::Int, self.depth);

        self.analyze_expr(body)?;
        if body.ty.kind != TyKind::Unit {
            return Err(self.type_error(body.pos));
        }

        self.exit_scope();
        Ok(TyKind::Unit)
    }

    fn analyze_let(&mut self, decls: &mut [Decl], body: &mut Expr) -> Result<TyKind> {
        self.enter_scope();
        self.analyze_decls(decls)?;
        self.analyze_expr(body)?;
        self.exit_scope();
        Ok(body.ty.kind.clone())
    }

    fn analyze_expr_seq(&mut self, exprs: &mut [Expr]) -> Result<TyKind> {
        let mut ty_kind = &TyKind::Unit;
        for expr in exprs {
            self.analyze_expr(expr)?;
            ty_kind = &expr.ty.kind;
        }
        Ok(ty_kind.clone())
    }

    fn analyze_var(&mut self, var: Symbol, pos: Pos) -> Result<TyKind> {
        let (ty, depth) = self
            .venv
            .look_var(var)
            .ok_or_else(|| Error::new(format!("Undefined var: {}", var.as_str()).into(), pos))?;

        self.func_context.maybe_push_free_var((var, ty, depth));
        Ok(ty.clone())
    }

    fn analyze_field_access(
        &mut self,
        lvalue: &mut Expr,
        field_name: Symbol,
        pos: Pos,
    ) -> Result<TyKind> {
        self.analyze_expr(lvalue)?;
        self.expect_lvalue(lvalue)?;

        if !lvalue.ty.kind.is_record() {
            return Err(self.type_error(lvalue.pos));
        }

        let field = lvalue.ty.kind.record_field_unchecked();
        let field = field
            .iter()
            .find(|(field, _)| field == &field_name)
            .ok_or_else(|| {
                Error::new(
                    format!("Invalid field access: {}", field_name.as_str()).into(),
                    pos,
                )
            })?;
        Ok(field.1.clone())
    }

    fn analyze_indexing(
        &mut self,
        lvalue: &mut Expr,
        index: &mut Expr,
        pos: Pos,
    ) -> Result<TyKind> {
        self.analyze_expr(lvalue)?;
        self.expect_lvalue(lvalue)?;
        if !lvalue.ty.kind.is_array() {
            return Err(self.type_error(pos));
        }

        self.analyze_expr(index)?;
        self.expect_int(index)?;

        Ok(lvalue.ty.kind.array_elem_unchecked().clone())
    }

    fn analyze_assign(&mut self, lvalue: &mut Expr, rhs: &mut Expr, pos: Pos) -> Result<TyKind> {
        self.analyze_expr(lvalue)?;
        self.expect_lvalue(lvalue)?;

        self.analyze_expr(rhs)?;

        self.try_type_promotion(&lvalue.ty.kind, &rhs.ty.kind, pos)?;
        Ok(rhs.ty.kind.clone())
    }

    fn resolve_type_alias(&mut self, decls: &[Decl]) -> Result<()> {
        let mut resolver = AliasResolver::new(&self.tenv);
        for decl in decls {
            match &decl.kind {
                DeclKind::TyDec { name, ty } => {
                    if !resolver.add_to_worklist(*name, &ty.kind) {
                        return Err(Error::new(
                            format!("Duplicated type name: {}", name.as_str()).into(),
                            decl.pos,
                        ));
                    }
                }
                _ => continue,
            }
        }

        let resolved = resolver.resolve()?;
        for (name, ty_kind) in resolved.into_iter() {
            self.tenv.insert(name, ty_kind, self.depth);
        }
        Ok(())
    }

    fn expect_int(&self, expr: &Expr) -> Result<()> {
        match &expr.ty.kind {
            TyKind::Int => Ok(()),
            _ => Err(Error::new("Expetcted integer type".into(), expr.pos)),
        }
    }

    fn expect_lvalue(&self, lvalue: &Expr) -> Result<()> {
        use ExprKind::*;
        match lvalue.kind {
            Var(..) | FieldAccess { .. } | Index { .. } => Ok(()),
            _ => Err(Error::new("Expected lvalue".into(), lvalue.pos)),
        }
    }

    fn try_type_promotion(&self, lhs: &TyKind, rhs: &TyKind, pos: Pos) -> Result<TyKind> {
        match (lhs, rhs) {
            (TyKind::Record { .. }, TyKind::Nil) => Ok(lhs.clone()),
            (TyKind::Nil, TyKind::Record { .. }) => Ok(rhs.clone()),
            (lhs, rhs) => {
                if lhs == rhs {
                    Ok(lhs.clone())
                } else {
                    Err(self.type_error(pos))
                }
            }
        }
    }

    fn resolve_alias(&self, ty: &TyKind, pos: Pos) -> Result<TyKind> {
        let kind = match ty {
            TyKind::Alias(symbol) => self
                .tenv
                .look(*symbol)
                .ok_or_else(|| {
                    Error::new(format!("Undefined type: {}", symbol.as_str()).into(), pos)
                })?
                .0
                .clone(),
            _ => ty.clone(),
        };
        Ok(kind)
    }

    fn type_error(&self, pos: Pos) -> Error {
        Error::new("Type Error".into(), pos)
    }

    fn enter_scope(&mut self) {
        self.venv.enter_scope();
        self.tenv.enter_scope();
        self.depth += 1;
    }

    fn exit_scope(&mut self) {
        self.depth -= 1;
        self.venv.exit_scope();
        self.tenv.exit_scope();
    }
}
