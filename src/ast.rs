use crate::impl_prelude::*;
use crate::ty::Ty;

pub struct Decl {
    pub kind: DeclKind,
    pub pos: Pos,
}

impl Decl {
    pub fn new(kind: DeclKind, pos: Pos) -> Self {
        Self { kind, pos }
    }
}

pub enum DeclKind {
    TyDec {
        name: Symbol,
        ty: Ty,
    },
    VarDec {
        name: Symbol,
        init: Expr,
        ty: Option<Ty>,
    },
    Function(Function),
}

pub struct Function {
    pub name: Symbol,
    pub args: Vec<(Symbol, Ty)>,
    pub ret_ty: Option<Ty>,
    pub body: Expr,
    pub free_variables: Vec<(Symbol, Ty)>,
}

impl Function {
    pub fn new(name: Symbol, args: Vec<(Symbol, Ty)>, ret_ty: Option<Ty>, body: Expr) -> Self {
        Self {
            name,
            args,
            ret_ty,
            body,
            free_variables: Vec::new(),
        }
    }

    pub fn append_free_variable(&mut self, var: Symbol, ty: Ty) {
        self.free_variables.push((var, ty));
    }
}

pub struct Expr {
    pub kind: ExprKind,
    pub pos: Pos,
}

impl Expr {
    pub fn new(kind: ExprKind, pos: Pos) -> Self {
        Expr { kind, pos }
    }

    pub fn binop(lhs: Expr, rhs: Expr, kind: BinOpKind) -> Self {
        let pos = lhs.pos + rhs.pos;
        let kind = ExprKind::BinOp {
            lhs: lhs.into(),
            rhs: rhs.into(),
            kind,
        };
        Expr::new(kind, pos)
    }

    pub fn unop(lhs: Expr, kind: UnOpKind, pos: Pos) -> Self {
        let kind = ExprKind::UnOp {
            lhs: lhs.into(),
            kind,
        };
        Expr::new(kind, pos)
    }

    pub fn lit(kind: LitKind, pos: Pos) -> Self {
        let kind = ExprKind::Lit(kind);
        Expr::new(kind, pos)
    }
}

pub enum ExprKind {
    BinOp {
        kind: BinOpKind,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    UnOp {
        kind: UnOpKind,
        lhs: Box<Expr>,
    },
    Lit(LitKind),
    Call {
        name: Symbol,
        args: Vec<Expr>,
    },
    Record {
        fields: Vec<(Symbol, Expr)>,
        ty: Ty,
    },
    Array {
        size: Box<Expr>,
        init: Box<Expr>,
        ty: Ty,
    },
    If {
        cond: Box<Expr>,
        then: Box<Expr>,
        else_: Option<Box<Expr>>,
    },
    While {
        cond: Box<Expr>,
        body: Box<Expr>,
    },
    For {
        var: Symbol,
        from: Box<Expr>,
        to: Box<Expr>,
        body: Box<Expr>,
    },
    Let {
        decls: Vec<Decl>,
        body: Box<Expr>,
    },
    Break,
    ExprSeq(Vec<Expr>),
    Var(Symbol),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Eq_,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    LogicalAnd,
    LogicalOr,
    Index,
    Assign,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnOpKind {
    Minus,
    FieldAccess(Symbol),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LitKind {
    LitStr(Symbol),
    Num(Symbol),
    Nil,
}
