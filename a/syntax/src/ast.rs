//! Abstract syntax tree (AST) types for the specification language.

/// AST node representing an entire file.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Document {
    /// All items defined in the document.
    pub items: Vec<DocumentItem>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// AST node for all top-level document items.
pub enum DocumentItem {
    /// A method declaration.
    Method(Method),
    /// A function declaration.
    Function(Function),
}

/// AST node representing a method.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    /// Method name.
    pub name: Ident,
    /// Input parameters.
    pub inputs: Vec<Var>,
    /// Output parameters.
    pub outputs: Vec<Var>,
    /// Pre- and postconditions
    pub specifications: Vec<Specification>,
    /// Method body.
    pub body: Option<Body>,
}

/// AST node representing a function.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    /// Function name.
    pub name: Ident,
    /// Input parameters.
    pub inputs: Vec<Var>,
    /// Return type.
    pub ret_ty: Type,
    /// Pre- and postconditions
    pub specifications: Vec<Specification>,
    /// Function body.
    pub body: Option<Expr>,
}

/// A pre- or postcondition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Specification {
    /// Imposed constraints on the input parameters.
    /// ```
    /// # let src = r#"
    /// method test(x: Int) requires x > 0
    /// # "#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    ///
    /// Preconditions are not allowed on output parameters.
    /// ```should_panic
    /// # let src = r#"
    /// // This is illegal
    /// method test() returns (x: Int) requires x > 0
    /// # "#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    Requires(Expr),
    /// Imposed constraints on parameters at the exit of the method.
    /// ```
    /// # let src = r#"
    /// method test() returns (x: Int) ensures x > 0
    /// # "#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    Ensures(Expr),
}

/// AST node for a sequence of statements.
///
/// Bodies are delimited by `'{'` and `'}'`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Body {
    /// The statements in the body
    pub statements: Vec<Statement>,
}

/// AST node for statements.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement {
    /// A variable declaration statement.
    ///
    /// ```
    /// # let src = r#"method test() {
    /// var x: Int
    /// # }"#;
    ///```
    ///
    /// Declarations can optionally also have initializers:
    /// ```
    /// # let src = r#"method test() {
    /// var x: Int := 17
    /// # }"#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    Var(Var, Option<Expr>),
    /// An assertion statement.
    ///
    /// ```
    /// # let src = r#"method test() {
    /// # var x: Int
    /// assert x > 10
    /// # }"#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    Assert(Expr),
    /// An assumption statement.
    ///
    /// ```
    /// # let src = r#"method test() {
    /// # var x: Int
    /// assume x > 10
    /// # }"#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    Assume(Expr),
    /// An assignment statement.
    ///
    /// ```
    /// # let src = r#"method test() {
    /// # var x: Int
    /// x := 42
    /// # }"#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    Assignment(Ident, Expr),
    /// Some methods output multiple values, in which case the variables are separated by commas:
    /// ```
    /// # let src = r#"
    /// method twoValues() returns (a: Int, b: Bool)
    /// # method test() {
    /// # var x: Int
    /// # var y: Bool
    /// // ...
    /// x, y := twoValues()
    /// # }"#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    MethodAssignment(Vec<Ident>, Ident, Vec<Expr>),
    /// An if statement, with optional else branch.
    ///
    /// ```
    /// # let src = r#"method test() {
    /// # var x: Int
    /// # var y: Int
    /// if (x > 10) { y := 15 } else { y := -2 }
    /// # }"#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    If(Expr, Body, Option<Body>),
    /// An if while, with optional loop invariants
    ///
    /// ```
    /// # let src = r#"method test() {
    /// # var x: Int
    /// # var y: Int
    /// while (x > 10)
    ///     invariant x >= 8
    /// {
    ///     x := x - 2
    /// }
    /// # }"#;
    /// # syntax::parse_src(src).unwrap();
    /// ```
    While {
        /// The loop condition.
        condition: Expr,
        /// Loop invariants.
        invariants: Vec<Expr>,
        /// Loop body.
        body: Body,
    },
    /// A nondeterministic choice statement.
    ///
    Choice(Body, Body),
}

/// A variable declaration.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var {
    /// Name of the variable.
    pub name: Ident,
    /// Type of the variable.
    pub ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Type's of expressions, variables, or, quantifiers.
pub enum Type {
    /// The integer type.
    Int,
    /// The boolean type.
    Bool,
}

/// AST node for all expressions in the language.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    /// The kind of the expression
    pub kind: Box<ExprKind>,
    /// The source location of the expression
    pub span: Span,
    /// The type of the expression
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// The kind of expression.
pub enum ExprKind {
    /// A boolean expression, containing a boolean literal.
    Boolean(bool),
    /// An integer expression, containing a numeric literal.
    Integer(String),
    /// A reference to the result value. Only useable in function postconditions.
    Result,
    /// A reference to a variable by name.
    Var(Ident),
    /// A call to a function with a list of arguments.
    Call(Ident, Vec<Expr>),
    /// A unary expression, such as `-x` and `!y`.
    Unary(UOp, Expr),
    /// A binary expression, such as `x && y`, `x + y`, and, `x ==> y`.
    Binary(Expr, Op, Expr),
    /// A quantification, such as `forall x: Int :: x > 0` or `exists y: Bool :: y ==> y`.
    Quantification(Quantifier, Var, Expr),
}
pub use ExprKind as EK;

/// A quantifier, either `exists` or `forall`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    /// Existence quantifier, `exists`.
    Exists,
    /// Universal quantifier, `forall`.
    Forall,
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    /// `&&`, has operand type `Bool` and produces a `Bool`.
    And,
    /// `/`, has operand type `Int` and produces a `Int`.
    Divide,
    /// `==`, has operand type `Bool` and produces a `Bool`.
    Eq,
    /// `>=`, has operand type `Int` and produces a `Bool`.
    Geq,
    /// `>`, has operand type `Int` and produces a `Bool`.
    Gt,
    /// `==>`, has operand type `Int` and produces a `Bool`.
    Implies,
    /// `<=`, has operand type `Int` and produces a `Bool`.
    Leq,
    /// `<`, has operand type `Int` and produces a `Bool`.
    Lt,
    /// `-`, has operand type `Int` and produces a `Int`.
    Minus,
    /// `!=`, has operand type `Int` and produces a `Bool`.
    Neq,
    /// `||`, has operand type `Bool` and produces a `Bool`.
    Or,
    /// `+`, has operand type `Int` and produces a `Int`.
    Plus,
    /// `*`, has operand type `Int` and produces a `Int`.
    Times,
}

/// A unary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UOp {
    /// A unary `-`, requires operand to have type `Int` and produces `Int`.
    Minus,
    /// A unary `!`, requires operand to have type `Bool` and produces `Bool`.
    Not,
}

#[derive(Clone, Eq)]
/// An identifier in the source file, associated with its source location.
///
/// All of its comparison-related trait impl's throw out the source location,
/// and only considers the identifier string.
pub struct Ident {
    /// The text string of the identifier
    pub text: String,
    /// The source location of the identifier
    pub span: Span,
}
impl std::hash::Hash for Ident {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.text.hash(state);
    }
}
impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.text.fmt(f)
    }
}
impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.text.fmt(f)
    }
}
impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.text == other.text
    }
}
impl std::ops::Deref for Ident {
    type Target = str;

    fn deref(&self) -> &str {
        &self.text
    }
}
impl From<Ident> for miette::SourceSpan {
    fn from(i: Ident) -> Self {
        i.span.into()
    }
}
impl From<Ident> for Span {
    fn from(i: Ident) -> Self {
        i.span
    }
}

/// A span in the original source document.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    start: usize,
    end: usize,
}

impl Span {
    /// Construct the zero span. This will be voided with any joins
    pub fn zero() -> Span {
        Self { start: 0, end: 0 }
    }
    /// Construct a new span starting at `start` and ending at `end`.
    pub fn start_end(start: usize, end: usize) -> Span {
        Self { start, end }
    }
    /// Construct a new span starting at `start` and ending at `start + len`.
    pub fn start_len(start: usize, len: usize) -> Span {
        Self {
            start,
            end: start + len,
        }
    }
    /// The start location in the source code.
    pub fn start(&self) -> usize {
        self.start
    }
    /// The end location in the source code.
    pub fn end(&self) -> usize {
        self.end
    }
    /// The length in bytes in the span.
    pub fn len(&self) -> usize {
        self.end - self.start
    }
    /// Returns true if the span contains zero bytes.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Returns the span containing the two spans. If either of the spans are
    /// empty, the other will be returned.
    pub fn join(self, other: Span) -> Span {
        if self.is_empty() {
            return other;
        }
        if other.is_empty() {
            return self;
        }
        Span::start_end(self.start().min(other.start()), self.end().max(other.end()))
    }
}
impl From<miette::SourceSpan> for Span {
    fn from(s: miette::SourceSpan) -> Self {
        Span::start_len(s.offset(), s.len())
    }
}
impl From<Span> for miette::SourceSpan {
    fn from(s: Span) -> Self {
        (s.start(), s.len()).into()
    }
}
impl FromIterator<Span> for Span {
    fn from_iter<T: IntoIterator<Item = Span>>(iter: T) -> Self {
        iter.into_iter()
            .filter(|s| !s.is_empty())
            .reduce(|a, b| a.join(b))
            .unwrap_or(Span { start: 0, end: 0 })
    }
}

impl ExprKind {
    pub(crate) fn parsed(self, ty: Type, p: usize, q: usize) -> Expr {
        self.boxed(ty, Span::start_end(p, q))
    }
    /// Wraps the expression kind in an `Expr` with the given type and span
    pub fn boxed(self, ty: Type, span: Span) -> Expr {
        Expr {
            kind: Box::new(self),
            span,
            ty,
        }
    }
}
impl Expr {
    /// Returns a reference to the expression kind
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }
}
impl From<&'_ Expr> for miette::SourceSpan {
    fn from(e: &'_ Expr) -> Self {
        e.span.into()
    }
}
impl From<&'_ Expr> for Span {
    fn from(e: &'_ Expr) -> Self {
        e.span
    }
}
