use crate::ast::{
    // IF ELSE dependences
    Body, Document, DocumentItem, Expr, Specification, Statement, ExprKind, UOp, Op, Type
};



/// 
#[derive(Debug)]
struct Encode1Context {
}

pub(crate) fn encode(doc: &Document) -> miette::Result<Document> {
    Encode1Context::encode(doc)
}

impl Encode1Context {
    fn encode(doc: & Document) -> miette::Result<Document> {
        let mut new_doc = doc.clone(); // Create a mutable copy of the document
        Self::add_output_decl(&mut new_doc)?;
        Self::add_input_decl(&mut new_doc)?;

        Self::replace_if(&mut new_doc)?;
        Self::add_postcondition(&mut new_doc)?;
        Self::add_precondition(&mut new_doc)?;

        Self::replace_assignments_with_assume(&mut new_doc)?;

        Ok(new_doc)
    }

    fn add_input_decl(doc: &mut Document) -> miette::Result<Document> {
        for item in &mut doc.items {
            if let DocumentItem::Method(method) = item {
                if let Some(body) = &mut method.body {
                    for input_var in &method.inputs {
                        let var_decl = Statement::Var(input_var.clone(), None);
                        body.statements.insert(0, var_decl);
                    }
                }
            }
        }
        Ok(doc.clone())
    }

    fn add_output_decl(doc: &mut Document) -> miette::Result<Document> {
        for item in &mut doc.items {
            if let DocumentItem::Method(method) = item {
                if let Some(body) = &mut method.body {
                    for input_var in &method.outputs {
                        let var_decl = Statement::Var(input_var.clone(), None);
                        body.statements.insert(0, var_decl);
                    }
                }
            }
        }
        Ok(doc.clone())
    }

    fn replace_if(doc: &mut Document) -> miette::Result<Document>{
        for item in &mut doc.items {
            if let DocumentItem::Method(method) = item {
                if let Some(body) = &mut method.body {
                    body.statements = body.statements.iter().map(|stmt| Self::encode_stmt(stmt)).collect();
                }
            }
        }
        Ok(doc.clone())
        
    }

    fn encode_stmt(stmt: &Statement) -> Statement {
        match stmt {
            Statement::If(cond, then, else_) => {
                let mut _then = then.clone();
                let mut _else_ = else_.clone().unwrap();
                
                let assumption1 = Statement::Assume(cond.clone());
                _then.statements.insert(0, assumption1);

                let not = UOp::Not;
                let mut expr = cond.clone();
                expr.kind = Box::new(ExprKind::Unary(not,cond.clone()));
                let assumption2 = Statement::Assume(expr.clone());
                _else_.statements.insert(0, assumption2);

                Statement::Choice(_then, _else_)
            },
            st => {
                (st).clone()
            }
        }
    }

    fn add_precondition(doc: &mut Document) -> miette::Result<Document> {
        for item in &mut doc.items {
            if let DocumentItem::Method(method) = item {
                for spec in &mut method.specifications{
                    if let Specification::Requires(expr) = spec {
                        let assumption = Statement::Assume(expr.clone());
                        let Some(body) = &mut method.body else { todo!() };

                        let mut index_after_var = 0;

                        for stmt in &mut body.statements{
                            if let Statement::Var(_var, _expr) = stmt { 
                                index_after_var += 1;
                            }
                            else{
                                break;
                            }
                        }
                        body.statements.insert(index_after_var, assumption);
                    }
                }
            }
        }
        Ok(doc.clone())
    }

    fn add_postcondition(doc: &mut Document) -> miette::Result<Document> {
        for item in &mut doc.items {
            if let DocumentItem::Method(method) = item {
                for spec in &mut method.specifications{
                    if let Specification::Ensures(expr) = spec {
                        let assertion = Statement::Assert(expr.clone());
                        let Some(body) = &mut method.body else { todo!() };
                        body.statements.push(assertion);
                    }
                }
            }
        }
        Ok(doc.clone())
    }

    fn replace_assignments_with_assume(doc: &mut Document) -> miette::Result<Document> {
        for item in &mut doc.items {
            if let DocumentItem::Method(method) = item {
                if let Some(body) = &mut method.body {
                    let mut new_statements = Vec::new();
    
                    for statement in &body.statements {
                        if let Statement::Assignment(ident, expr) = statement {
                            let new_ident = Expr {
                                kind: Box::new(ExprKind::Var(ident.clone())),
                                span: expr.span.clone(),
                                ty: expr.ty.clone(),
                            };
                            let new_binary = ExprKind::Binary(new_ident.clone(), Op::Eq, expr.clone());
                            let mut new_expr = expr.clone();
                            new_expr.kind = Box::new(new_binary);
                            new_expr.ty = Type::Bool;
                            let assumption = Statement::Assume(new_expr.clone());
                            new_statements.push(assumption);
                        } else {
                            new_statements.push(statement.clone());
                        }
                    }
    
                    body.statements = new_statements;
                }
            }
        }
        Ok(doc.clone())
    }
    


}
