use crate::ast::{Document, Span};

lalrpop_util::lalrpop_mod!(parser, "/parser.rs");

pub fn parse_document(src: &str) -> Result<Document, ParseError> {
    static PARSER: once_cell::sync::Lazy<parser::DocumentParser> =
        once_cell::sync::Lazy::new(parser::DocumentParser::new);

    match PARSER.parse(src) {
        Ok(p) => Ok(p),
        Err(e) => Err(ParseError::new(src, e)),
    }
}

#[derive(Debug, thiserror::Error, miette::Diagnostic, Clone)]
pub enum ParseError {
    #[error("Invalid Token")]
    InvalidToken {
        #[source_code]
        src: String,
        #[label("This token is not valid in this context")]
        err_span: Span,
    },
    #[error("Unrecognized Token")]
    #[diagnostic(help("Expected tokens here are: {expected}"))]
    UnrecognizedToken {
        #[source_code]
        src: String,
        #[label = "The token \"{token}\" is unrecognized in this context."]
        err_span: Span,
        token: String,
        expected: String,
    },
    #[error("Unrecognized EOF")]
    #[diagnostic(help("Expected tokens in this context are:\n{expected}"))]
    UnrecognizedEof {
        #[source_code]
        src: String,
        #[label = "The document ends too early. Are you missing a token?"]
        err_span: Span,
        expected: String,
    },
    #[error("Assignment of non-function expression to multiple variable")]
    #[diagnostic(help("Only methods allow assignment to multiple variables"))]
    ExprAssignmentToMultipleVars {
        #[source_code]
        src: String,
        #[label = "The assignment to multiple variables occurs here, but only one is allowed"]
        err_span: Span,
    },
}

impl ParseError {
    fn new(
        src: &str,
        e: lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token, Self>,
    ) -> Self {
        let prep_src = || format!("{}\n", src);

        match e {
            lalrpop_util::ParseError::InvalidToken { location } => ParseError::InvalidToken {
                src: prep_src(),
                err_span: Span::start_len(location, 0),
            },
            lalrpop_util::ParseError::UnrecognizedEof { location, expected } => {
                ParseError::UnrecognizedEof {
                    src: prep_src(),
                    err_span: Span::start_len(location, 0),
                    expected: expected.join(", "),
                }
            }
            lalrpop_util::ParseError::UnrecognizedToken { token, expected } => {
                ParseError::UnrecognizedToken {
                    src: prep_src(),
                    err_span: Span::start_end(token.0, token.2),
                    token: token.1.to_string(),
                    expected: expected.join(", "),
                }
            }
            lalrpop_util::ParseError::ExtraToken { .. } => todo!(),
            lalrpop_util::ParseError::User { error } => match error {
                ParseError::ExprAssignmentToMultipleVars { err_span, .. } => {
                    ParseError::ExprAssignmentToMultipleVars {
                        src: prep_src(),
                        err_span,
                    }
                }
                _ => error,
            },
        }
    }
}

#[test]
fn parse_all_examples() -> miette::Result<()> {
    use std::fs;

    for dir in fs::read_dir("../examples").unwrap() {
        for f in fs::read_dir(dir.unwrap().path()).unwrap() {
            let f = f.unwrap();
            match f.path().extension() {
                Some(e) if e == "vpr" => {}
                _ => continue,
            }

            let src = fs::read_to_string(f.path()).unwrap();

            let _ = parse_document(&src)?;
        }
    }

    Ok(())
}
