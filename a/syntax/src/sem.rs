use std::collections::HashMap;

use miette::{bail, ensure};

use crate::ast::{
    Body, Document, DocumentItem, Expr, Function, Ident, Method, Op, Quantifier, Span,
    Specification, Statement, Type, UOp, Var, EK,
};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Location {
    Pred { in_pre: bool, fun_ret: Option<Type> },
    Expr,
}

impl Expr {
    fn expect_ty(self, span: Span, expected: Type) -> miette::Result<Expr> {
        self.ty.expect_ty(span, expected)?;
        Ok(self)
    }
}
impl Type {
    fn expect_ty(self, span: Span, expected: Type) -> miette::Result<()> {
        ensure!(
            self == expected,
            TypeMismatch {
                expected,
                actual: self,
                span,
            }
        );
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum Deceleration {
    Input(Var),
    Output(Var),
    Var(Var),
    Quantifier(Quantifier, Var),
}
impl Deceleration {
    fn var(&self) -> &Var {
        use Deceleration::*;

        match self {
            Input(var) | Output(var) | Var(var) | Quantifier(_, var) => var,
        }
    }
}

#[derive(Debug)]
enum LookupItem<'a> {
    Decl(Deceleration),
    Method(&'a Method),
    Function(&'a Function),
}
impl LookupItem<'_> {
    fn name(&self) -> &Ident {
        match self {
            LookupItem::Decl(d) => &d.var().name,
            LookupItem::Method(m) => &m.name,
            LookupItem::Function(f) => &f.name,
        }
    }
}

#[derive(Debug)]
struct AnalysisContext<'a> {
    methods: HashMap<Ident, &'a Method>,
    functions: HashMap<Ident, &'a Function>,
    local_decls: HashMap<Ident, Deceleration>,
}

pub(crate) fn analyze(doc: &Document) -> miette::Result<Document> {
    AnalysisContext::analyze(doc)
}

impl<'a> AnalysisContext<'a> {
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

    fn analyze_stmt(&mut self, stmt: &Statement) -> miette::Result<Statement> {
        match stmt {
            Statement::Var(var, initializer) => {
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
                Ok(Statement::Var(var.clone(), initializer.clone()))
            }
            Statement::Assert(pred) => {
                let ty = self.analyze_expr(
                    Location::Pred {
                        fun_ret: None,
                        in_pre: false,
                    },
                    pred,
                )?;
                ty.expect_ty(pred.span, Type::Bool)?;
                Ok(Statement::Assert(pred.clone()))
            }
            Statement::Assume(pred) => {
                let ty = self.analyze_expr(
                    Location::Pred {
                        fun_ret: None,
                        in_pre: false,
                    },
                    pred,
                )?;
                ty.expect_ty(pred.span, Type::Bool)?;
                Ok(Statement::Assume(pred.clone()))
            }
            Statement::Assignment(var, expr) => {
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

                Ok(Statement::Assignment(var.clone(), expr.with_ty(decl.ty)))
            }
            Statement::MethodAssignment(vars, name, args) => {
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

                            return self.analyze_stmt(&Statement::Assignment(
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

                Ok(Statement::MethodAssignment(
                    vars.clone(),
                    name.clone(),
                    args.clone(),
                ))
            }
            Statement::If(cond, then, else_) => {
                let cond_ty = self.analyze_expr(Location::Expr, cond)?;
                cond_ty.expect_ty(cond.span, Type::Bool)?;

                let then = self.analyze_body(then)?;

                let else_ = if let Some(else_) = else_.as_ref() {
                    Some(self.analyze_body(else_)?)
                } else {
                    None
                };

                Ok(Statement::If(cond.clone(), then, else_))
            }
            Statement::While {
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

                Ok(Statement::While {
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

use SemError::*;

#[derive(Debug, thiserror::Error, miette::Diagnostic, Clone)]
enum SemError {
    #[error("Duplicate declaration of method '{first}'")]
    DuplicateMethodDeclaration {
        #[label("First time")]
        first: Ident,
        #[label("Second time")]
        second: Ident,
    },
    #[error("Duplicate declaration of function '{first}'")]
    DuplicateFunctionDeclaration {
        #[label("First time")]
        first: Ident,
        #[label("Second time")]
        second: Ident,
    },
    #[error("Duplicate declaration of '{first}'")]
    DuplicateDeclaration {
        #[label("First declaration")]
        first: Ident,
        #[label("Second declaration")]
        second: Ident,
    },
    #[error("Variable '{var}' used in precondition")]
    VariableInPredicate {
        #[label("Used here")]
        var: Ident,
        #[label("Declared here")]
        declared: Ident,
    },
    #[error("Output parameter '{var}' is used in precondition")]
    OutputInPrecondition {
        #[label("Used here")]
        var: Ident,
        #[label("Declared here")]
        declared: Ident,
    },
    #[error("The `result` value used outside of function postcondition")]
    ResultUsedNotInPostFun {
        #[label("Used here, which is not in function postcondition")]
        span: Span,
    },
    #[error("Undeclared variable '{var}'")]
    UndeclaredVariable {
        #[label]
        var: Ident,
    },
    #[error("Wrong number of inputs. Expected '{expected}' and was given '{actual}'")]
    WrongNumberOfInputs {
        expected: usize,
        actual: usize,
        #[label("Called here")]
        call: Ident,
        #[label("Defined here")]
        def: Ident,
    },
    #[error("Type mismatch. Expected '{expected:?}' but found '{actual:?}'")]
    TypeMismatch {
        expected: Type,
        actual: Type,
        #[label(
            "This expression was expected to have type '{expected:?}' but has type '{actual:?}'"
        )]
        span: Span,
    },
    #[error("Wrong number of variables in assignment. The expression produces {outputs} output(s), but is assigned to {actual}")]
    WrongNumberOfVariablesInAssignment {
        outputs: usize,
        actual: usize,
        #[label("Must have {outputs} variable(s), found {actual}")]
        assign_span: Span,
    },
    #[error("Illegal to assign to input '{input}'")]
    AssignmentToInput {
        #[label("This is an assignment to '{input}' of input")]
        input: Ident,
        #[label("The input parameter is declared here")]
        decl_span: Span,
    },
    #[error("Tried to a quantified variable variable '{var}'")]
    AssignmentToQuantifier {
        #[label("Assigned here")]
        var: Ident,
    },
    #[error("Tried to assign to an undeclared variable '{var}'")]
    AssignmentToUndeclared {
        #[label("Assigned here")]
        var: Ident,
    },
    #[error("Tried to assign to a method '{name}'")]
    AssignmentToMethod {
        #[label("Assigned here")]
        name: Ident,
    },
    #[error("Tried to assign to a function '{name}'")]
    AssignmentToFunction {
        #[label("Assigned here")]
        name: Ident,
    },
    #[error("Tried to call a variable '{name}'")]
    CallToVariable {
        #[label("Function or method called here")]
        name: Ident,
    },
    #[error("The method '{name}' was called in expression position, which is illegal. Consider using a function instead.")]
    MethodCallInExpr {
        #[label("Method called here")]
        name: Ident,
    },
    #[error("Call to undefined function/method '{name}'")]
    CallToUndefined {
        #[label("Function or method called here")]
        name: Ident,
    },
    #[error("Variable '{first}' declared multiple times")]
    VariableAlreadyDeclared {
        #[label("First time")]
        first: Ident,
        #[label("Second time")]
        second: Ident,
    },
    #[error("Quantifier used in expression position")]
    QuantifierInExpr {
        #[label("Quantifier defined here, which is in expression position")]
        var: Ident,
    },
    #[error("Implication used in expression position, but is only allowed in predicate")]
    ImplicationInExpr {
        #[label("Implication used here, which is in expression position")]
        span: Span,
    },
}

#[cfg(test)]
mod tests {
    use crate::{parse_file, parse_src};

    #[test]
    fn sem_analyze_all_examples() -> miette::Result<()> {
        use std::fs;

        for dir in fs::read_dir("../examples").unwrap() {
            for f in fs::read_dir(dir.unwrap().path()).unwrap() {
                let f = f.unwrap();
                match f.path().extension() {
                    Some(e) if e == "vpr" => {}
                    _ => continue,
                }

                parse_file(f.path())?;
            }
        }

        Ok(())
    }

    macro_rules! sem_ok {
        ($name:tt, $src:literal) => {
            #[test]
            fn $name() -> miette::Result<()> {
                parse_src($src)?;
                Ok(())
            }
        };
    }
    macro_rules! sem_err {
        ($name:tt, $src:literal) => {
            #[test]
            #[should_panic]
            fn $name() {
                parse_src($src).unwrap();
            }
        };
    }

    sem_ok!(
        output_assignment,
        "method test() returns (output: Int) { output := 42 }"
    );
    sem_err!(input_assignment, "method test(input: Int) { input := 42 }");
    sem_err!(
        output_in_precondition,
        "method test() returns (output: Int) requires output > 0"
    );
    sem_err!(
        hidden_output_in_precondition,
        "method test() returns (x: Int) requires fn(x > 0)
         method fn(b: Bool) returns (r: Bool)"
    );
    sem_ok!(
        quantifier_in_precondition,
        "method test() returns (x: Int) requires forall y: Int :: y > 0"
    );
    sem_err!(
        undeclared_method,
        "method test() returns (output: Int) { output := ohNo() }"
    );
    sem_err!(
        wrong_input_number,
        "method hello(input: Int) returns (output: Int)
         method test() returns (output: Int) { output := hello() }"
    );
    sem_ok!(
        correct_input_number,
        "method hello(input: Int) returns (output: Int)
         method test() returns (output: Int) { output := hello(12) }"
    );
    sem_err!(
        wrong_output_number_1,
        "method hello() returns (output: Int)
         method test() returns (a: Int, b: Int) { a, b := hello() }"
    );
    sem_err!(
        wrong_output_number_2,
        "method hello() returns (a: Int, b: Int)
         method test() returns (a: Int) { a := hello() }"
    );
    sem_ok!(
        correct_output_number_1,
        "method hello() returns (a: Int)
         method test() returns (a: Int) { a := hello() }"
    );
    sem_ok!(
        correct_output_number_2,
        "method hello() returns (a: Int, b: Int)
         method test() returns (a: Int, b: Int) { a, b := hello() }"
    );
    sem_ok!(quantifiers, "method test() requires forall x: Int :: true");
    sem_err!(
        quantifier_in_expr,
        "method test() { var x: Int := forall y: Int :: true }"
    );
    sem_err!(
        quantifier_clash,
        "method test(x: Int) requires forall x: Int :: true"
    );
    sem_err!(
        declared_both_input_and_output,
        "method test(x: Int) returns (x: Int)"
    );
    sem_err!(
        duplicate_var_in_branches,
        "method test() { if (true) { var x: Int } else { var x: Int } }"
    );
    sem_err!(
        adding_booleans,
        "method test() { var x: Int := true + false }"
    );
    sem_err!(anding_ints, "method test() { var x: Bool := 1 && 2 }");
    sem_err!(
        assign_expr_to_multi,
        "method test() returns (x: Int, y: Int) { x, y := 2 }"
    );
    sem_err!(
        method_not_allowed_in_expr,
        "method test() returns (x: Int) method using() returns (y: Int) { y := test() + 1 }"
    );
    sem_ok!(
        function_allowed_in_expr,
        "function test(): Int method using() returns (y: Int) { y := test() + 1 }"
    );
    sem_ok!(
        function_assignment,
        "function test(): Int method using() returns (y: Int) { y := test() }"
    );
    sem_err!(imp_in_expr, "function test(): Bool { true ==> false }");
    sem_ok!(
        result_in_postcondition,
        "function test(): Bool ensures result ==> true"
    );
    sem_err!(
        result_in_precondition,
        "function test(): Bool requires result ==> true"
    );
    sem_err!(
        result_in_method_postcondition,
        "method test() ensures result ==> true"
    );
    sem_err!(
        result_in_method_precondition,
        "method test() requires result ==> true"
    );
    sem_ok!(
        assert_predicate,
        "method test() { assert forall x: Int :: x > 0 }"
    );
    sem_err!(
        assert_integer, 
        "method test() { assert 3 }"
    );
    sem_ok!(
        assume_predicate,
        "method test() { assume forall x: Int :: x > 0 }"
    );
    sem_err!(
        assume_integer, 
        "method test() { assume 3 }"
    );
}
