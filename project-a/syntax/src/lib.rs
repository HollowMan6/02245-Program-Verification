#![warn(missing_docs)]
//! Parsing and static analysis of the miniviper language.
//!
//! ```
//! # let src = r#"
//! method sum(n: Int) returns (res: Int)
//!   requires 0 <= n
//!   ensures  res == n * (n + 1) / 2
//! {
//!   res := 0
//!   var i: Int := 0
//!   while(i <= n)
//!     invariant i <= (n + 1)
//!     invariant res == (i - 1) * i / 2
//!   {
//!     res := res + i
//!     i := i + 1
//!   }
//! }
//! # "#;
//! # syntax::parse_src(src).unwrap();
//! ```

pub mod ast;
mod ast_ext;
mod parse;
mod sem;

use miette::IntoDiagnostic;

/// Parse and statically analyze a file. The returned document type-checks and
/// contains no illegal assignments or references.
///
/// ```
/// # fn main() -> miette::Result<()> {
/// let file = "../examples/03-bonus/sum.vpr";
/// let ast = syntax::parse_file(file)?;
/// # Ok(())
/// # }
/// ```
pub fn parse_file(f: impl AsRef<std::path::Path>) -> miette::Result<ast::Document> {
    use miette::Context;

    let f = f.as_ref();
    let src = std::fs::read_to_string(f)
        .into_diagnostic()
        .with_context(|| format!("Reading file {f:?}"))?;
    let ast = parse::parse_document(&src)?;
    sem::analyze(&ast)
        .with_context(|| format!("Parsing {f:?}"))
        .map_err(|e| e.with_source_code(src))
}
/// Parse and statically analyze a string. The returned document type-checks and
/// contains no illegal assignments or references.
///
/// For reading files, see [parse_file].
///
/// ```
/// # fn main() -> miette::Result<()> {
/// let src = "method hello(a: Int) requires a > 0";
/// let ast = syntax::parse_src(src)?;
/// # Ok(())
/// # }
/// ```
pub fn parse_src(src: impl AsRef<str>) -> miette::Result<ast::Document> {
    let src = src.as_ref();
    let ast = parse::parse_document(src)?;
    sem::analyze(&ast).map_err(|e| e.with_source_code(src.to_string()))
}
