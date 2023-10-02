use crate::ast::{Expr, ExprKind, Op, Span, Type};

impl Expr {
    /// Creates a new boolean expression.
    pub fn bool(b: bool, span: Option<Span>) -> Expr {
        ExprKind::Boolean(b).boxed(Type::Bool, span.unwrap_or_else(|| Span::start_len(0, 0)))
    }

    /// Creates a new int expression.
    pub fn int(i: i64, span: Option<Span>) -> Expr {
        ExprKind::Integer(i.to_string())
            .boxed(Type::Int, span.unwrap_or_else(|| Span::start_len(0, 0)))
    }

    /// Returns a new expressions with the same span and kind, but with the given type
    pub fn with_ty(&self, ty: Type) -> Expr {
        Expr {
            kind: self.kind.clone(),
            span: self.span,
            ty,
        }
    }

    /// Return `self` `op` `other` with the span being the union of the two expressions.
    pub fn binary_op(&self, op: Op, other: &Expr) -> Expr {
        let ty = match op {
            Op::And | Op::Eq | Op::Geq | Op::Gt | Op::Implies | Op::Leq | Op::Lt | Op::Or => {
                Type::Bool
            }
            Op::Divide | Op::Minus | Op::Neq | Op::Plus | Op::Times => Type::Int,
        };
        ExprKind::Binary(self.clone(), op, other.clone()).boxed(ty, self.span.join(other.span))
    }

    /// Return `self ==> other` with the span being the union of the two expressions.
    pub fn implies(&self, other: &Expr) -> Expr {
        self.binary_op(Op::Implies, other)
    }

    /// Return `self == other` with the span being the union of the two expressions.
    pub fn _eq(&self, other: &Expr) -> Expr {
        self.binary_op(Op::Eq, other)
    }

    /// Return `self != other` with the span being the union of the two expressions.
    pub fn _neq(&self, other: &Expr) -> Expr {
        self.binary_op(Op::Neq, other)
    }

    /// Return `self < other` with the span being the union of the two expressions.
    pub fn _lt(&self, other: &Expr) -> Expr {
        self.binary_op(Op::Lt, other)
    }

    /// Return `self <= other` with the span being the union of the two expressions.
    pub fn _leq(&self, other: &Expr) -> Expr {
        self.binary_op(Op::Leq, other)
    }

    /// Return `self > other` with the span being the union of the two expressions.
    pub fn _gt(&self, other: &Expr) -> Expr {
        self.binary_op(Op::Gt, other)
    }

    /// Return `self >= other` with the span being the union of the two expressions.
    pub fn _geq(&self, other: &Expr) -> Expr {
        self.binary_op(Op::Geq, other)
    }
}
