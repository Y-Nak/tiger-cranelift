use crate::ast::*;
use crate::impl_prelude::*;
use crate::lexer::{Lexer, Token, TokenKind};

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    ty_unique_id: u32,
}

impl<'a> Parser<'a> {
    pub fn new(code: &'a [u8]) -> Result<Self> {
        Ok(Self {
            lexer: Lexer::new(code)?,
            ty_unique_id: 0,
        })
    }

    pub fn parse(&mut self) -> Result<Expr> {
        let expr = self.parse_expr()?;
        self.expect(TokenKind::Eof)?;
        Ok(expr)
    }

    fn parse_expr(&mut self) -> Result<Expr> {
        if let Some(if_token) = self.eat_kw(kw::If)? {
            self.parse_if(if_token)
        } else if let Some(while_token) = self.eat_kw(kw::While)? {
            self.parse_while(while_token)
        } else if let Some(for_token) = self.eat_kw(kw::For)? {
            self.parse_for(for_token)
        } else if let Some(let_token) = self.eat_kw(kw::Let)? {
            self.parse_let(let_token)
        } else if let Some(br_token) = self.eat_kw(kw::Break)? {
            Ok(Expr::new(ExprKind::Break, br_token.pos))
        } else if let Some(lp_token) = self.eat(TokenKind::LParen)? {
            if self.eat(TokenKind::RParen)?.is_some() {
                return Ok(Expr::new(
                    ExprKind::ExprSeq(vec![]),
                    lp_token.pos + self.current_pos(),
                ));
            }

            let mut exprs = vec![self.parse_expr()?];
            while self.eat(TokenKind::SemiColon)?.is_some() {
                exprs.push(self.parse_expr()?);
            }
            self.expect(TokenKind::RParen)?;

            Ok(Expr::new(
                ExprKind::ExprSeq(exprs),
                lp_token.pos + self.current_pos(),
            ))
        } else {
            self.parse_logical_or()
        }
    }

    fn parse_if(&mut self, if_token: Token) -> Result<Expr> {
        // Parse if-condition.
        let cond = self.parse_expr()?;

        // Parse then clause.
        self.expect_kw(kw::Then)?;
        let then = self.parse_expr()?;

        // Parse else_ clause if exists.
        let else_ = if self.eat_kw(kw::Else)?.is_some() {
            let else_ = self.parse_expr()?;
            Some(else_)
        } else {
            None
        };

        let kind = ExprKind::If {
            cond: cond.into(),
            then: then.into(),
            else_: else_.map(|else_| else_.into()),
        };
        Ok(Expr::new(kind, if_token.pos + self.current_pos()))
    }

    fn parse_while(&mut self, while_token: Token) -> Result<Expr> {
        // Parse while body.
        let cond = self.parse_expr()?;

        // Parse while-condition.
        self.expect_kw(kw::Do)?;
        let body = self.parse_expr()?;

        let kind = ExprKind::While {
            cond: cond.into(),
            body: body.into(),
        };

        Ok(Expr::new(kind, while_token.pos + self.current_pos()))
    }

    fn parse_for(&mut self, for_token: Token) -> Result<Expr> {
        let (var, _) = self.expect_var()?;

        // Parse for-from value.
        self.expect(TokenKind::ColonEq)?;
        let from = self.parse_expr()?;

        // Parse for-to value.
        self.expect_kw(kw::To)?;
        let to = self.parse_expr()?;

        // Parse body.
        self.expect_kw(kw::Do)?;
        let body = self.parse_expr()?;

        let kind = ExprKind::For {
            var,
            from: from.into(),
            to: to.into(),
            body: body.into(),
        };

        Ok(Expr::new(kind, for_token.pos + self.current_pos()))
    }

    fn parse_let(&mut self, let_token: Token) -> Result<Expr> {
        let mut decls = Vec::new();
        while self.eat_kw(kw::In)?.is_none() {
            decls.push(self.parse_decl()?);
        }

        let expr_start_pos = self.current_pos();
        let (expr_seq, expr_pos) = if self.eat_kw(kw::End)?.is_some() {
            (vec![], expr_start_pos)
        } else {
            let mut expr_seq = vec![self.parse_expr()?];
            while self.eat(TokenKind::SemiColon)?.is_some() {
                expr_seq.push(self.parse_expr()?);
            }
            let expr_pos = expr_start_pos + self.current_pos();
            self.expect_kw(kw::End)?;
            (expr_seq, expr_pos)
        };

        let body = Expr::new(ExprKind::ExprSeq(expr_seq), expr_pos);
        let kind = ExprKind::Let {
            decls,
            body: body.into(),
        };
        Ok(Expr::new(kind, let_token.pos + self.current_pos()))
    }

    fn parse_logical_or(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_logical_and()?;
        while self.eat(TokenKind::Or)?.is_some() {
            let rhs = self.parse_logical_and()?;
            lhs = Expr::binop(lhs, rhs, BinOpKind::LogicalOr);
        }
        Ok(lhs)
    }

    fn parse_logical_and(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_relational()?;
        while self.eat(TokenKind::And)?.is_some() {
            let rhs = self.parse_relational()?;
            lhs = Expr::binop(lhs, rhs, BinOpKind::LogicalAnd);
        }
        Ok(lhs)
    }

    fn parse_relational(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_term()?;
        loop {
            let binop_kind = match self.lexer.peek_token().kind {
                TokenKind::Lt => BinOpKind::Lt,
                TokenKind::Le => BinOpKind::Le,
                TokenKind::Gt => BinOpKind::Gt,
                TokenKind::Ge => BinOpKind::Ge,
                TokenKind::Eq_ => BinOpKind::Eq_,
                TokenKind::Ne => BinOpKind::Ne,
                _ => break,
            };
            self.lexer.next_token()?;
            let rhs = self.parse_term()?;
            lhs = Expr::binop(lhs, rhs, binop_kind);
        }
        Ok(lhs)
    }

    fn parse_term(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_factor()?;
        loop {
            let binop_kind = match self.lexer.peek_token().kind {
                TokenKind::Plus => BinOpKind::Add,
                TokenKind::Minus => BinOpKind::Sub,
                _ => break,
            };
            self.lexer.next_token()?;
            let rhs = self.parse_term()?;
            lhs = Expr::binop(lhs, rhs, binop_kind);
        }
        Ok(lhs)
    }

    fn parse_factor(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_unop()?;
        loop {
            let binop_kind = match self.lexer.peek_token().kind {
                TokenKind::Star => BinOpKind::Mul,
                TokenKind::Slash => BinOpKind::Div,
                _ => break,
            };
            self.lexer.next_token()?;
            let rhs = self.parse_unop()?;
            lhs = Expr::binop(lhs, rhs, binop_kind);
        }
        Ok(lhs)
    }

    fn parse_unop(&mut self) -> Result<Expr> {
        if let Some(token) = self.eat(TokenKind::Minus)? {
            let lhs = self.parse_primary()?;
            Ok(Expr::unop(
                lhs,
                UnOpKind::Minus,
                token.pos + self.current_pos(),
            ))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<Expr> {
        if let Some(nil_token) = self.eat_kw(kw::Nil)? {
            Ok(Expr::lit(LitKind::Nil, nil_token.pos))
        } else if let Some((symbol, pos)) = self.eat_num()? {
            Ok(Expr::lit(LitKind::Num(symbol), pos))
        } else if let Some((symbol, pos)) = self.eat_litstr()? {
            Ok(Expr::lit(LitKind::LitStr(symbol), pos))
        } else {
            let (var, pos) = self.expect_var()?;
            self.parse_postfix(var, pos)
        }
    }

    fn parse_postfix(&mut self, name: Symbol, pos: Pos) -> Result<Expr> {
        let lvalue = if self.eat(TokenKind::LParen)?.is_some() {
            // Parse call expr.
            let args = self.parse_args()?;
            return Ok(Expr::new(
                ExprKind::Call { name, args },
                pos + self.current_pos(),
            ));
        } else if self.eat(TokenKind::LBracket)?.is_some() {
            // Parse array initalization or indexing.
            let expr = self.parse_expr()?;
            self.expect(TokenKind::RBracket)?;
            if self.eat_kw(kw::Of)?.is_some() {
                // Parse array initialization.
                let init = self.parse_expr()?;
                let kind = ExprKind::Array {
                    size: expr.into(),
                    init: init.into(),
                    ty: Ty::new(TyKind::Alias(name), pos),
                };
                return Ok(Expr::new(kind, pos + self.current_pos()));
            } else {
                // Parse indexing.
                let var = Expr::new(ExprKind::Var(name), pos);
                let kind = ExprKind::Index {
                    lvalue: var.into(),
                    index: expr.into(),
                };
                let lvalue = Expr::new(kind, pos + self.current_pos());
                self.parse_access(lvalue)?
            }
        } else if self.eat(TokenKind::LBrace)?.is_some() {
            // Parse record initialization.
            let fields = self.parse_record_init()?;
            let kind = ExprKind::Record {
                fields,
                ty: Ty::new(TyKind::Alias(name), pos),
            };
            return Ok(Expr::new(kind, pos + self.current_pos()));
        } else if self.eat(TokenKind::Dot)?.is_some() {
            // Parse field access.
            let (field, _) = self.expect_var()?;
            let var = Expr::new(ExprKind::Var(name), pos);
            let kind = ExprKind::FieldAccess {
                lvalue: var.into(),
                field,
            };
            let lvalue = Expr::new(kind, pos + self.current_pos());
            self.parse_access(lvalue)?
        } else {
            // Parse s.imple var
            Expr::new(ExprKind::Var(name), pos)
        };

        // Parse assign operator if exists.
        if self.eat(TokenKind::ColonEq)?.is_some() {
            let rhs = self.parse_expr()?;
            let kind = ExprKind::Assign {
                lvalue: lvalue.into(),
                rhs: rhs.into(),
            };
            Ok(Expr::new(kind, pos + self.current_pos()))
        } else {
            Ok(lvalue)
        }
    }

    fn parse_access(&mut self, mut lvalue: Expr) -> Result<Expr> {
        let pos = lvalue.pos;
        if self.eat(TokenKind::Dot)?.is_some() {
            let (field, _) = self.expect_var()?;
            let kind = ExprKind::FieldAccess {
                lvalue: lvalue.into(),
                field,
            };
            lvalue = Expr::new(kind, pos + self.current_pos());
            self.parse_access(lvalue)
        } else if self.eat(TokenKind::LBracket)?.is_some() {
            let index = self.parse_expr()?;
            let kind = ExprKind::Index {
                lvalue: lvalue.into(),
                index: index.into(),
            };
            lvalue = Expr::new(kind, pos + self.current_pos());
            self.parse_access(lvalue)
        } else {
            Ok(lvalue)
        }
    }

    fn parse_args(&mut self) -> Result<Vec<Expr>> {
        if self.eat(TokenKind::RParen)?.is_some() {
            return Ok(vec![]);
        }

        let mut args = vec![self.parse_expr()?];
        while self.eat(TokenKind::Comma)?.is_some() {
            args.push(self.parse_expr()?);
        }
        self.expect(TokenKind::RParen)?;
        Ok(args)
    }

    fn parse_decl(&mut self) -> Result<Decl> {
        if let Some(ty_token) = self.eat_kw(kw::Type)? {
            let (name, _) = self.expect_var()?;
            self.expect(TokenKind::Eq_)?;
            let ty = self.parse_ty()?;
            let kind = DeclKind::TyDec { name, ty };
            Ok(Decl::new(kind, ty_token.pos + self.current_pos()))
        } else if let Some(var_token) = self.eat_kw(kw::Var)? {
            self.parse_var_dec(var_token.pos)
        } else if let Some(func_token) = self.eat_kw(kw::Function)? {
            self.parse_func_dec(func_token.pos)
        } else {
            Err(Error::new(
                "Expected declaration".into(),
                self.current_pos(),
            ))
        }
    }

    fn parse_ty(&mut self) -> Result<Ty> {
        if let Some(lb_token) = self.eat(TokenKind::LBrace)? {
            let field: Vec<(Symbol, TyKind)> = self
                .parse_ty_fields()?
                .into_iter()
                .map(|(name, ty)| (name, ty.kind))
                .collect();
            self.expect(TokenKind::RBrace)?;

            let ty_kind = TyKind::Record {
                field,
                unique: self.ty_unique_id,
            };
            let ty = Ty::new(ty_kind, lb_token.pos + self.current_pos());
            self.ty_unique_id += 1;
            Ok(ty)
        } else if let Some(array_token) = self.eat_kw(kw::Array)? {
            self.expect_kw(kw::Of)?;
            let (ty_ref, _) = self.expect_var()?;
            let elem_ty = Box::new(TyKind::Alias(ty_ref));

            let ty_kind = TyKind::Array {
                elem_ty,
                unique: self.ty_unique_id,
            };
            let ty = Ty::new(ty_kind, array_token.pos + self.current_pos());
            self.ty_unique_id += 1;
            Ok(ty)
        } else {
            self.parse_ty_alias()
        }
    }

    fn parse_var_dec(&mut self, pos: Pos) -> Result<Decl> {
        let (name, _) = self.expect_var()?;

        // Parse ty if exists.
        let ty = if self.eat(TokenKind::Colon)?.is_some() {
            Some(self.parse_ty_alias()?)
        } else {
            None
        };

        // Parse init.
        self.expect(TokenKind::ColonEq)?;
        let init = self.parse_expr()?;

        let kind = DeclKind::VarDec { name, init, ty };
        Ok(Decl::new(kind, pos + self.current_pos()))
    }

    fn parse_func_dec(&mut self, pos: Pos) -> Result<Decl> {
        let (name, _) = self.expect_var()?;

        // Parse arg declaration.
        self.expect(TokenKind::LParen)?;
        let args = self.parse_ty_fields()?;
        self.expect(TokenKind::RParen)?;

        // Parse return type if exists.
        let ret_ty = if self.eat(TokenKind::Colon)?.is_some() {
            self.parse_ty_alias()?
        } else {
            Ty::new(TyKind::Unit, Pos::dummy())
        };

        // Parse body.
        self.expect(TokenKind::Eq_)?;
        let body = self.parse_expr()?;
        let func = Function::new(name, args, ret_ty, body);
        let kind = DeclKind::Function(func);
        Ok(Decl::new(kind, pos + self.current_pos()))
    }

    fn parse_ty_fields(&mut self) -> Result<Vec<(Symbol, Ty)>> {
        let mut fields = Vec::new();
        while let Some((symbol, _)) = self.eat_var()? {
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_ty()?;
            fields.push((symbol, ty));
            if self.eat(TokenKind::Comma)?.is_none() {
                break;
            }
        }
        Ok(fields)
    }

    fn parse_record_init(&mut self) -> Result<Vec<(Symbol, Expr)>> {
        if self.eat(TokenKind::RBrace)?.is_some() {
            return Ok(vec![]);
        }

        // Parse first entry.
        let id = self.expect_var()?.0;
        self.expect(TokenKind::Eq_)?;
        let expr = self.parse_expr()?;

        let mut init = vec![(id, expr)];
        while self.eat(TokenKind::Comma)?.is_some() {
            let id = self.expect_var()?.0;
            self.expect(TokenKind::Eq_)?;
            let expr = self.parse_expr()?;
            init.push((id, expr));
        }

        self.expect(TokenKind::RBrace)?;
        Ok(init)
    }

    fn parse_ty_alias(&mut self) -> Result<Ty> {
        let (ty_ref, pos) = self.expect_var()?;
        Ok(Ty::new(TyKind::Alias(ty_ref), pos))
    }

    fn eat(&mut self, kind: TokenKind) -> Result<Option<Token>> {
        if self.lexer.peek_token().kind == kind {
            Ok(Some(self.lexer.next_token()?))
        } else {
            Ok(None)
        }
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token> {
        self.eat(kind)?.ok_or_else(|| {
            Error::new(
                format!("Expected {}", kind.as_str()).into(),
                self.current_pos(),
            )
        })
    }

    fn eat_kw(&mut self, kw: Symbol) -> Result<Option<Token>> {
        self.eat(TokenKind::Ident(kw))
    }

    fn expect_kw(&mut self, kw: Symbol) -> Result<Token> {
        self.eat_kw(kw)?.ok_or_else(|| {
            Error::new(
                format!("Expected {}", kw.as_str()).into(),
                self.current_pos(),
            )
        })
    }

    fn eat_var(&mut self) -> Result<Option<(Symbol, Pos)>> {
        let token = self.lexer.peek_token();
        match token.kind.var() {
            Some(symbol) => {
                self.lexer.next_token()?;
                Ok(Some((symbol, token.pos)))
            }
            None => Ok(None),
        }
    }

    fn expect_var(&mut self) -> Result<(Symbol, Pos)> {
        let token = self.lexer.next_token()?;
        match token.kind.var() {
            Some(symbol) => Ok((symbol, token.pos)),
            None => Err(Error::new("Expected variable".into(), token.pos)),
        }
    }

    fn eat_num(&mut self) -> Result<Option<(Symbol, Pos)>> {
        let token = self.lexer.peek_token();
        match token.kind.num() {
            Some(symbol) => {
                self.lexer.next_token()?;
                Ok(Some((symbol, token.pos)))
            }
            None => Ok(None),
        }
    }

    fn eat_litstr(&mut self) -> Result<Option<(Symbol, Pos)>> {
        let token = self.lexer.peek_token();
        match token.kind.litstr() {
            Some(symbol) => {
                self.lexer.next_token()?;
                Ok(Some((symbol, token.pos)))
            }
            None => Ok(None),
        }
    }

    fn current_pos(&self) -> Pos {
        self.lexer.current_pos()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(code: &str) -> Expr {
        let mut parser = Parser::new(code.as_bytes()).unwrap();
        parser.parse().unwrap()
    }

    fn extract_binop(expr: Expr) -> (BinOpKind, Expr, Expr) {
        match expr.kind {
            ExprKind::BinOp { kind, lhs, rhs } => (kind, *lhs, *rhs),
            _ => panic!(),
        }
    }

    fn extract_alias_ty(ty: &TyKind) -> &str {
        match ty {
            &TyKind::Alias(name) => name.as_str(),
            _ => panic!(),
        }
    }

    fn extract_record_ty(ty: Ty) -> Vec<(Symbol, TyKind)> {
        match ty.kind {
            TyKind::Record { field, .. } => field,
            _ => panic!(),
        }
    }

    fn extract_array_ty(ty: Ty) -> TyKind {
        match ty.kind {
            TyKind::Array { elem_ty, .. } => *elem_ty,
            _ => panic!(),
        }
    }

    fn extract_decl_ty(decl: Decl) -> (Symbol, Ty) {
        match decl.kind {
            DeclKind::TyDec { name, ty } => (name, ty),
            _ => panic!(),
        }
    }

    fn extract_expr_seq(expr: Expr) -> Vec<Expr> {
        match expr.kind {
            ExprKind::ExprSeq(exprs) => exprs,
            _ => panic!(),
        }
    }

    fn extract_let_expr(expr: Expr) -> (Vec<Decl>, Vec<Expr>) {
        match expr.kind {
            ExprKind::Let { decls, body } => (decls, extract_expr_seq(*body)),
            _ => panic!(),
        }
    }

    fn assert_ty_field(field: Vec<(Symbol, TyKind)>, expect: Vec<(&str, &str)>) {
        assert_eq!(field.len(), expect.len());
        for (f, e) in field.into_iter().zip(expect.into_iter()) {
            assert_eq!(f.0.as_str(), e.0);
            assert_eq!(extract_alias_ty(&f.1), e.1);
        }
    }

    #[test]
    fn test_binop() {
        let code = "10 + 20";
        let expr = parse(code);
        let (kind, ..) = extract_binop(expr);
        assert_eq!(kind, BinOpKind::Add);
    }

    #[test]
    fn test_priority() {
        let code = "10 * 20 + 30 <> 10 & 20 | 1";
        let mut expr = parse(code);
        for expect in vec![
            BinOpKind::LogicalOr,
            BinOpKind::LogicalAnd,
            BinOpKind::Ne,
            BinOpKind::Add,
            BinOpKind::Mul,
        ] {
            let (kind, lhs, _) = extract_binop(expr);
            assert_eq!(kind, expect);
            expr = lhs;
        }
    }

    #[test]
    fn test_call() {
        let code = "tiger_func(t1 * t1, t2 + t3)";
        let expr = parse(code);
        match expr.kind {
            ExprKind::Call { name, mut args } => {
                assert_eq!(name.as_str(), "tiger_func");
                assert_eq!(args.len(), 2);
                assert_eq!(extract_binop(args.remove(0)).0, BinOpKind::Mul);
                assert_eq!(extract_binop(args.remove(0)).0, BinOpKind::Add);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_array_init() {
        let code = "int [N + 10] of a * a";
        let expr = parse(code);
        match expr.kind {
            ExprKind::Array { size, init, ty } => {
                assert_eq!(extract_binop(*size).0, BinOpKind::Add);
                assert_eq!(extract_binop(*init).0, BinOpKind::Mul);
                assert_eq!(extract_alias_ty(&ty.kind), "int");
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_record_init() {
        let code = "my_record {id1 = a + 10, id2 = b - 10}";
        let expr = parse(code);
        match expr.kind {
            ExprKind::Record { mut fields, ty } => {
                assert_eq!(fields.len(), 2);
                let field = fields.remove(0);
                assert_eq!(extract_binop(field.1).0, BinOpKind::Add);
                assert_eq!(field.0.as_str(), "id1");
                let field = fields.remove(0);
                assert_eq!(extract_binop(field.1).0, BinOpKind::Sub);
                assert_eq!(field.0.as_str(), "id2");

                assert_eq!(extract_alias_ty(&ty.kind), "my_record");
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_indexing() {
        let code = "arr[10]";
        let expr = parse(code);
        match expr.kind {
            ExprKind::Index { .. } => {}
            _ => panic!("Index"),
        }
    }

    #[test]
    fn test_if() {
        let code = "if a > 20 then
                        30 + 20
                    else
                        30 - 20
                    ";
        let expr = parse(code);
        match expr.kind {
            ExprKind::If { cond, then, else_ } => {
                assert_eq!(extract_binop(*cond).0, BinOpKind::Gt);
                assert_eq!(extract_binop(*then).0, BinOpKind::Add);
                assert_eq!(extract_binop(*else_.unwrap()).0, BinOpKind::Sub);
            }
            _ => panic!(),
        };
    }

    #[test]
    fn test_for() {
        let code = "for x := a + 1 to a * a do
                        b := a + b
                   ";
        let expr = parse(code);
        match expr.kind {
            ExprKind::For {
                var,
                from,
                to,
                body,
            } => {
                assert_eq!("x", var.as_str());
                assert_eq!(extract_binop(*from).0, BinOpKind::Add);
                assert_eq!(extract_binop(*to).0, BinOpKind::Mul);
                match body.kind {
                    ExprKind::Assign { .. } => {}
                    _ => panic!("Assign"),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_while() {
        let code = "while x <= 20 do
                        x := x + 1
                   ";
        let expr = parse(code);
        match expr.kind {
            ExprKind::While { cond, body } => {
                assert_eq!(extract_binop(*cond).0, BinOpKind::Le);
                match body.kind {
                    ExprKind::Assign { .. } => {}
                    _ => panic!("Assign"),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_expr_seq() {
        let code = "(
                     1 + 20;
                     20 * 1
                     )";
        let expr = parse(code);
        let mut seq = extract_expr_seq(expr);

        assert_eq!(seq.len(), 2);
        assert_eq!(extract_binop(seq.remove(0)).0, BinOpKind::Add);
        assert_eq!(extract_binop(seq.remove(0)).0, BinOpKind::Mul);
    }

    #[test]
    fn test_let_with_ty_dec() {
        let code = "let
                        type record_type = {id1: int, id2: string}
                        type array_type = array of record_type
                        type alias_ty = array_type
                    in
                    end
                    ";
        let expr = parse(code);
        let (mut decls, _) = extract_let_expr(expr);

        assert_eq!(decls.len(), 3);
        let (name, ty) = extract_decl_ty(decls.remove(0));
        assert_eq!(name.as_str(), "record_type");
        let field = extract_record_ty(ty);
        assert_ty_field(field, vec![("id1", "int"), ("id2", "string")]);

        let (name, ty) = extract_decl_ty(decls.remove(0));
        assert_eq!(name.as_str(), "array_type");
        let ty = extract_array_ty(ty);
        assert_eq!(extract_alias_ty(&ty), "record_type");

        let (name, ty) = extract_decl_ty(decls.remove(0));
        assert_eq!(name.as_str(), "alias_ty");
        assert_eq!(extract_alias_ty(&ty.kind), "array_type");
    }

    #[test]
    fn test_let_with_var_dec() {
        let code = "let
                        var my_var: int := 10 * 20
                    in
                    end
                    ";

        let expr = parse(code);
        let (mut decls, _) = extract_let_expr(expr);
        assert_eq!(decls.len(), 1);
        match decls.remove(0).kind {
            DeclKind::VarDec { name, init, ty } => {
                assert_eq!(name.as_str(), "my_var");
                assert_eq!(extract_binop(init).0, BinOpKind::Mul);
                assert_eq!(extract_alias_ty(&ty.unwrap().kind), "int");
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_let_with_func_dec() {
        let code = "let
                        function add(a: int, b:int): int =
                            a + b
                    in
                    end
                    ";
        let expr = parse(code);
        let (mut decls, _) = extract_let_expr(expr);

        assert_eq!(decls.len(), 1);
        match decls.remove(0).kind {
            DeclKind::Function(func) => {
                assert_eq!(func.name.as_str(), "add");
                let args = func
                    .args
                    .into_iter()
                    .map(|(name, ty)| (name, ty.kind))
                    .collect();
                assert_ty_field(args, vec![("a", "int"), ("b", "int")]);
                assert_eq!(extract_alias_ty(&func.ret_ty.kind), "int");
                assert_eq!(extract_binop(func.body).0, BinOpKind::Add);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_let_body() {
        let code = "let
                        var x := 10
                    in
                        x + 1;
                        x - 1
                    end
                   ";
        let expr = parse(code);
        let (_, mut body) = extract_let_expr(expr);

        assert_eq!(body.len(), 2);

        assert_eq!(extract_binop(body.remove(0)).0, BinOpKind::Add);
        assert_eq!(extract_binop(body.remove(0)).0, BinOpKind::Sub);
    }
}
