# 02245-rust-template

A Rust template for working on project A of the course [02245 — Program Verification](http://courses.compute.dtu.dk/02245/). It includes a parser and static analyzer for the input format *MicroViper* (see example below), with nice error reporting.

```vpr
method sum(n: Int) returns (res: Int)
  requires 0 <= n
  ensures  res == n * (n + 1) / 2
{
  res := 0
  var i: Int := 0
  while(i <= n)
    invariant i <= (n + 1)
    invariant res == (i - 1) * i / 2
  {
    res := res + i
    i := i + 1
  }
}
```

## Getting started

For building the template, you will need to have the following installed:

- [Rust](https://www.rust-lang.org/tools/install) (v1.63 or later)
- [CMake](https://cmake.org/install/)
- [Python](https://realpython.com/installing-python/)

The project also uses [Z3](https://github.com/Z3Prover/z3), but that will be installed automatically by cargo.

With all the requirements installed, run the following to check that everything is set up correctly:

```bash
$ # all tests should pass
$ cargo test --all
$ # this opens the projects and all dependencies documentation
$ cargo doc --open
```

### Setting up on macOS

If you already have some dependencies installed those can be skipped, but the following should let you get up and running from scratch:

```bash
$ brew install rustup cmake python
$ # choose the installation method you prefer. stable/default should be fine.
$ rustup-init
```

## Project structure

- The `syntax` module defines the Abstract Syntax Tree (AST) for the input language, which also does semantic analysis before returning the AST.
    - It uses [LALRPOP](https://github.com/lalrpop/lalrpop/) for parsing,
    - [miette](https://github.com/zkat/miette) for error reporting.
- `src/main.rs` is the entry point for interacting with the project. Use `cargo run` and pass a list of files to parse and analyze.
    - To parse and analyze all the included examples run
    ```bash
    $ cargo run examples/**/*.vpr
    ```
    - The main function returns [`miette::Result<()>`](https://docs.rs/miette/latest/miette/type.Result.html), which allows the [try operator (`?`)](https://blog.rust-lang.org/2016/11/10/Rust-1.13.html#the--operator) to be used in main and possibly in the rest of the project to get nice error reporting. Read the [miette docs](https://docs.rs/miette/latest/miette/index.html) for more details.
