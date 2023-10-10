
use crate::ast::*;


/// AST node for statements.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement1 {
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
    /// A nondeterministic choice statement.
    ///
    Choice(Body, Body),
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
}



#[derive(Debug)]
struct AnalysisContext1<'a> {
    methods: HashMap<Ident, &'a Method>,
    functions: HashMap<Ident, &'a Function>,
    local_decls: HashMap<Ident, Deceleration>,
}

pub(crate) fn analyze(doc: &Document) -> miette::Result<Document> {
    AnalysisContext1::analyze(doc)
}

impl<'a> AnalysisContext1<'a> {
    fn analyze(doc: &'a Document) -> miette::Result<Document> {
        let mut ctx = Self {
            methods: Default::default(),
            functions: Default::default(),
            local_decls: Default::default(),
        };

        // NOTE: First pass registers all methods
        for item in &doc.items {
            match item {
                DocumentItem::Method(method) => {
                    if let Some(old) = ctx.lookup(&method.name) {
                        bail!(DuplicateMethodDeclaration {
                            first: old.name().clone(),
                            second: method.name.clone(),
                        })
                    }
                    ctx.methods.insert(method.name.clone(), method);
                }
                DocumentItem::Function(function) => {
                    if let Some(old) = ctx.lookup(&function.name) {
                        bail!(DuplicateFunctionDeclaration {
                            first: old.name().clone(),
                            second: function.name.clone(),
                        })
                    }
                    ctx.functions.insert(function.name.clone(), function);
                }
            }
        }

        // NOTE: Second pass analyzes the methods
        let items = doc
            .items
            .iter()
            .map(|item| {
                Ok(match item {
                    DocumentItem::Method(method) => {
                        DocumentItem::Method(ctx.analyze_method(method)?)
                    }
                    DocumentItem::Function(function) => {
                        DocumentItem::Function(ctx.analyze_function(function)?)
                    }
                })
            })
            .collect::<miette::Result<_>>()?;

        Ok(Document { items })
    }
    fn analyze_method(&mut self, method: &Method) -> miette::Result<Method> {
        // NOTE: Reset local decls
        self.local_decls = Default::default();
        for input in &method.inputs {
            if let Some(old) = self.lookup(&input.name) {
                bail!(DuplicateDeclaration {
                    first: old.name().clone(),
                    second: input.name.clone()
                })
            }

            self.local_decls
                .insert(input.name.clone(), Deceleration::Input(input.clone()));
        }
        for output in &method.outputs {
            if let Some(old) = self.lookup(&output.name) {
                bail!(DuplicateDeclaration {
                    first: old.name().clone(),
                    second: output.name.clone()
                })
            }

            self.local_decls
                .insert(output.name.clone(), Deceleration::Output(output.clone()));
        }

        for spec in &method.specifications {
            self.analyze_spec(None, spec)?;
        }

        let body = if let Some(body) = method.body.as_ref() {
            Some(self.analyze_body(body)?)
        } else {
            None
        };

        Ok(Method {
            name: method.name.clone(),
            inputs: method.inputs.clone(),
            outputs: method.outputs.clone(),
            specifications: method.specifications.clone(),
            body,
        })
    }
    fn analyze_function(&mut self, function: &Function) -> miette::Result<Function> {
        // NOTE: Reset local decls
        self.local_decls = Default::default();
        for input in &function.inputs {
            if let Some(old) = self.lookup(&input.name) {
                bail!(DuplicateDeclaration {
                    first: old.name().clone(),
                    second: input.name.clone()
                })
            }

            self.local_decls
                .insert(input.name.clone(), Deceleration::Input(input.clone()));
        }

        for spec in &function.specifications {
            self.analyze_spec(Some(function.ret_ty), spec)?;
        }

        let body = if let Some(body) = function.body.as_ref() {
            Some(
                self.analyze_expr(Location::Expr, body)?
                    .expect_ty(body.span, function.ret_ty)?,
            )
        } else {
            None
        };

        Ok(Function {
            body,
            ..function.clone()
        })
    }

    fn lookup(&self, name: &Ident) -> Option<LookupItem> {
        self.methods
            .get(name)
            .map(|m| LookupItem::Method(m))
            .or_else(|| self.functions.get(name).map(|i| LookupItem::Function(i)))
            .or_else(|| {
                self.local_decls
                    .get(name)
                    .map(|i| LookupItem::Decl(i.clone()))
            })
    }

    fn analyze_spec(&mut self, fun_ret: Option<Type>, spec: &Specification) -> miette::Result<()> {
        let (p, in_pre) = match spec {
            Specification::Requires(p) => (p, true),
            Specification::Ensures(p) => (p, false),
        };

        self.analyze_expr(Location::Pred { in_pre, fun_ret }, p)?
            .expect_ty(p.span, Type::Bool)?;
        Ok(())
    }

    fn analyze_body(&mut self, body: &Body) -> miette::Result<Body> {
        Ok(Body {
            statements: body
                .statements
                .iter()
                .map(|stmt| self.analyze_stmt(stmt))
                .collect::<miette::Result<_>>()?,
        })
    }

    fn analyze_stmt(&mut self, stmt: &Statement1) -> miette::Result<Statement1> {
        match stmt {
            Statement1::Var(var, initializer) => {
                if let Some(old) = self.lookup(&var.name) {
                    bail!(VariableAlreadyDeclared {
                        first: old.name().clone(),
                        second: var.name.clone(),
                    });
                }
                self.local_decls
                    .insert(var.name.clone(), Deceleration::Var(var.clone()));
                if let Some(init) = initializer {
                    let init_ty = self.analyze_expr(Location::Expr, init)?;
                    init_ty.expect_ty(init.span, var.ty)?;
                }
                Ok(Statement1::Var(var.clone(), initializer.clone()))
            }
            Statement1::Assert(pred) => {
                let ty = self.analyze_expr(
                    Location::Pred {
                        fun_ret: None,
                        in_pre: false,
                    },
                    pred,
                )?;
                ty.expect_ty(pred.span, Type::Bool)?;
                Ok(Statement1::Assert(pred.clone()))
            }
            Statement1::Assume(pred) => {
                let ty = self.analyze_expr(
                    Location::Pred {
                        fun_ret: None,
                        in_pre: false,
                    },
                    pred,
                )?;
                ty.expect_ty(pred.span, Type::Bool)?;
                Ok(Statement1::Assume(pred.clone()))
            }
            Statement1::Assignment(var, expr) => {
                let decl = match self.lookup(var) {
                    Some(LookupItem::Decl(decl)) => match decl {
                        Deceleration::Input(inp) => {
                            bail!(AssignmentToInput {
                                input: var.clone(),
                                decl_span: inp.name.span,
                            })
                        }
                        Deceleration::Var(var) | Deceleration::Output(var) => var,
                        Deceleration::Quantifier(_, _) => {
                            bail!(AssignmentToQuantifier { var: var.clone() })
                        }
                    },
                    Some(LookupItem::Function(_)) => {
                        bail!(AssignmentToFunction { name: var.clone() })
                    }
                    Some(LookupItem::Method(_)) => bail!(AssignmentToMethod { name: var.clone() }),
                    None => bail!(AssignmentToUndeclared { var: var.clone() }),
                };

                self.analyze_expr(Location::Expr, expr)?
                    .expect_ty(expr.span, decl.ty)?;

                Ok(Statement1::Assignment(var.clone(), expr.with_ty(decl.ty)))
            }
            Statement1::MethodAssignment(vars, name, args) => {
                let m = if let Some(m) = self.lookup(name) {
                    match m {
                        LookupItem::Decl(_) => bail!(CallToVariable { name: name.clone() }),
                        LookupItem::Method(m) => m,
                        LookupItem::Function(_) => {
                            // NOTE: Rewrite statement to  `var := function(...args)`
                            if vars.len() > 1 {
                                bail!(WrongNumberOfVariablesInAssignment {
                                    outputs: 1,
                                    actual: vars.len(),
                                    assign_span: vars.iter().map(|v| v.span).collect(),
                                });
                            }

                            let span = name.span.join(vars.iter().map(|v| v.span).collect());

                            return self.analyze_stmt(&Statement1::Assignment(
                                vars[0].clone(),
                                EK::Call(name.clone(), args.clone()).boxed(Type::Int, span),
                            ));
                        }
                    }
                } else {
                    bail!(CallToUndefined { name: name.clone() })
                };

                let vars_ty = vars
                    .iter()
                    .map(|var| match self.lookup(var) {
                        Some(LookupItem::Function(_)) => {
                            bail!(AssignmentToFunction { name: name.clone() })
                        }
                        Some(LookupItem::Method(_)) => {
                            bail!(AssignmentToMethod { name: name.clone() })
                        }
                        Some(LookupItem::Decl(decl)) => match decl {
                            Deceleration::Input(inp) => {
                                bail!(AssignmentToInput {
                                    input: var.clone(),
                                    decl_span: inp.name.span,
                                })
                            }
                            Deceleration::Var(var) | Deceleration::Output(var) => Ok(var),
                            Deceleration::Quantifier(_, _) => {
                                bail!(AssignmentToQuantifier { var: var.clone() })
                            }
                        },
                        None => bail!(AssignmentToUndeclared { var: var.clone() }),
                    })
                    .collect::<miette::Result<Vec<_>>>()?;

                ensure!(
                    vars.len() == m.outputs.len(),
                    WrongNumberOfVariablesInAssignment {
                        outputs: m.outputs.len(),
                        actual: vars.len(),
                        assign_span: vars.iter().map(|v| v.span).collect(),
                    }
                );

                for (var, output) in vars_ty.iter().zip(&m.outputs) {
                    var.ty.expect_ty(var.name.span, output.ty)?;
                }

                ensure!(
                    args.len() == m.inputs.len(),
                    WrongNumberOfInputs {
                        expected: m.inputs.len(),
                        actual: args.len(),
                        call: name.clone(),
                        def: m.name.clone()
                    }
                );

                for (arg, input) in args.iter().zip(&m.inputs.clone()) {
                    self.analyze_expr(Location::Expr, arg)?
                        .expect_ty(arg.span, input.ty)?;
                }

                Ok(Statement1::MethodAssignment(
                    vars.clone(),
                    name.clone(),
                    args.clone(),
                ))
            }
            Statement1::If(cond, then, else_) => {
                let cond_ty = self.analyze_expr(Location::Expr, cond)?;
                cond_ty.expect_ty(cond.span, Type::Bool)?;

                let then = self.analyze_body(then)?;

                let else_ = if let Some(else_) = else_.as_ref() {
                    Some(self.analyze_body(else_)?)
                } else {
                    None
                };
                Ok(Statement1::Choice(then, else_))
                // Ok(Statement1::If(cond.clone(), then, else_))
            }
            Statement1::While {
                condition,
                invariants,
                body,
            } => {
                let cond_ty = self.analyze_expr(Location::Expr, condition)?;
                cond_ty.expect_ty(condition.span, Type::Bool)?;

                for inv in invariants {
                    self.analyze_expr(
                        Location::Pred {
                            fun_ret: None,
                            in_pre: false,
                        },
                        inv,
                    )?
                    .expect_ty(inv.span, Type::Bool)?;
                }

                let body = self.analyze_body(body)?;

                Ok(Statement1::While {
                    condition: condition.clone(),
                    invariants: invariants.clone(),
                    body,
                })
            }
        }
    }

    fn analyze_expr(&mut self, loc: Location, expr: &Expr) -> miette::Result<Expr> {
        let (kind, ty) = match expr.kind() {
            kind @ EK::Boolean(_) => (kind.clone(), Type::Bool),
            kind @ EK::Integer(_) => (kind.clone(), Type::Int),
            EK::Result => match loc {
                Location::Pred {
                    in_pre: false,
                    fun_ret: Some(ret_ty),
                } => (EK::Result, ret_ty),
                _ => bail!(ResultUsedNotInPostFun { span: expr.span }),
            },
            EK::Var(var) => {
                if let Some(decl) = self.local_decls.get(var) {
                    use Deceleration::*;
                    use Location::*;

                    match (loc, decl) {
                        (Pred { in_pre: true, .. }, Output(dec)) => bail!(OutputInPrecondition {
                            var: var.clone(),
                            declared: dec.name.clone(),
                        }),
                        (Pred { in_pre: true, .. }, Var(dec)) => bail!(VariableInPredicate {
                            var: var.clone(),
                            declared: dec.name.clone(),
                        }),

                        (_, Input(dec) | Output(dec) | Var(dec) | Quantifier(_, dec)) => {
                            (EK::Var(var.clone()), dec.ty)
                        }
                    }
                } else {
                    bail!(UndeclaredVariable { var: var.clone() })
                }
            }
            EK::Call(fun, inputs) => match self.lookup(fun) {
                Some(LookupItem::Decl(_)) => bail!(CallToVariable { name: fun.clone() }),
                Some(LookupItem::Method(_)) => bail!(MethodCallInExpr { name: fun.clone() }),
                Some(LookupItem::Function(function)) => {
                    ensure!(
                        function.inputs.len() == inputs.len(),
                        WrongNumberOfInputs {
                            expected: function.inputs.len(),
                            actual: inputs.len(),
                            call: fun.clone(),
                            def: function.name.clone()
                        }
                    );

                    let ret_ty = function.ret_ty;

                    let inputs = function
                        .inputs
                        .clone()
                        .iter()
                        .zip(inputs)
                        .map(|(input, x)| {
                            self.analyze_expr(Location::Expr, x)?
                                .expect_ty(x.span, input.ty)
                        })
                        .collect::<miette::Result<Vec<_>>>()?;

                    (EK::Call(fun.clone(), inputs), ret_ty)
                }
                None => bail!(CallToUndefined { name: fun.clone() }),
            },
            EK::Unary(uop, x) => {
                use UOp::*;

                let (operand_ty, out_ty) = match uop {
                    Minus => (Type::Int, Type::Int),
                    Not => (Type::Bool, Type::Bool),
                };

                let x = self.analyze_expr(loc, x)?.expect_ty(x.span, operand_ty)?;
                (EK::Unary(*uop, x), out_ty)
            }
            EK::Binary(l, op, r) => {
                use Op::*;

                if loc == Location::Expr {
                    ensure!(op != &Implies, ImplicationInExpr { span: expr.span });
                }

                let (operand_ty, out_ty) = match op {
                    And | Or | Implies => (Type::Bool, Type::Bool),
                    Neq | Eq | Geq | Leq | Gt | Lt => (Type::Int, Type::Bool),
                    Divide | Minus | Plus | Times => (Type::Int, Type::Int),
                };

                let l = self
                    .analyze_expr(loc.clone(), l)?
                    .expect_ty(l.span, operand_ty)?;
                let r = self.analyze_expr(loc, r)?.expect_ty(r.span, operand_ty)?;

                (EK::Binary(l, *op, r), out_ty)
            }
            EK::Quantification(quant, free, inner) => {
                ensure!(
                    loc != Location::Expr,
                    QuantifierInExpr {
                        var: free.name.clone(),
                    }
                );

                if let Some(old) = self.lookup(&free.name) {
                    bail!(DuplicateDeclaration {
                        first: old.name().clone(),
                        second: free.name.clone()
                    });
                }

                self.local_decls.insert(
                    free.name.clone(),
                    Deceleration::Quantifier(*quant, free.clone()),
                );

                let inner = self
                    .analyze_expr(loc, inner)?
                    .expect_ty(inner.span, Type::Bool)?;

                (EK::Quantification(*quant, free.clone(), inner), Type::Bool)
            }
        };

        Ok(kind.boxed(ty, expr.span))
    }
}