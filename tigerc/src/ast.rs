use crate::impl_prelude::*;

pub struct Decl {
    pub kind: DeclKind,
    pub pos: Pos,
}

impl Decl {
    pub fn new(kind: DeclKind, pos: Pos) -> Self {
        Self { kind, pos }
    }

    pub fn is_func(&self) -> bool {
        match self.kind {
            DeclKind::Function(..) => true,
            _ => false,
        }
    }

    pub fn extract_func_unchecked(self) -> Function {
        match self.kind {
            DeclKind::Function(func) => *func,
            _ => panic!(),
        }
    }
}

pub enum DeclKind {
    TyDec { name: Symbol, ty: Ty },
    VarDec(Box<VarDec>),
    Function(Box<Function>),
}

pub struct VarDec {
    pub name: Symbol,
    pub init: Expr,
    pub ty: Option<Ty>,
}

pub struct Function {
    pub name: Symbol,
    pub args: Vec<(Symbol, Ty)>,
    pub ret_ty: Ty,
    pub body: Expr,
    pub free_variables: Vec<(Symbol, TyKind)>,
}

impl Function {
    pub fn new(name: Symbol, args: Vec<(Symbol, Ty)>, ret_ty: Ty, body: Expr) -> Self {
        Self {
            name,
            args,
            ret_ty,
            body,
            free_variables: Vec::new(),
        }
    }
}

pub struct Expr {
    pub kind: ExprKind,
    pub pos: Pos,
    pub ty: Ty,
}

impl Expr {
    pub fn new(kind: ExprKind, pos: Pos) -> Self {
        Expr {
            kind,
            pos,
            ty: Ty::new(TyKind::Invalid, Pos::dummy()),
        }
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
        elem_ty: Ty,
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
    FieldAccess {
        lvalue: Box<Expr>,
        field: Symbol,
    },
    Index {
        lvalue: Box<Expr>,
        index: Box<Expr>,
    },
    Assign {
        lvalue: Box<Expr>,
        rhs: Box<Expr>,
    },
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
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnOpKind {
    Minus,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LitKind {
    LitStr(Symbol),
    Num(Symbol),
    Nil,
}
