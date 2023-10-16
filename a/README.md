# (A) Building a Verifier

> Group: 2
> - s233508: Jawad Zaheer
> - s233511: Songlin Jiang

An automated verification tool in Rust for MicroViper – a subset of the language supported by the Viper verification infrastructure. It includes a parser and static analyzer for the input format *MicroViper* (see example below), with nice error reporting. The code is for [project A](https://pv.cmath.eu/projects/construction.html) of the course [02245 — Program Verification](http://courses.compute.dtu.dk/02245/).

<!-- 
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
``` -->

## Supported Features

- [X] Core Feature 1: Support MicroViper programs that consist of a single method, where the method body is loop-free and contains no recursive method calls and all expressions are built-in (i.e. no user-defined functions).
- [X] Core Feature 2: Whenever verification fails, your verifier should indicate which assertions, invariants, or postconditions could not be verified.
- [X] Core Feature 3: Support reasoning about partial correctness of while loops.
- [ ] Extension Feature 1: Support partial correctness verification of multiple (and possibly mutally recursive) methods.
- [ ] Extension Feature 2: Support user-defined functions that can be defined by providing a function body, or pre- and postconditions, or both. (Hint: Recall that function bodies and calls are expressions, that is, function calls may appear in specifications.)
- [ ] Extension Feature 3: Use efficient weakest preconditions in your MicroViper verifier. Provide sufficiently large examples to demonstrate support of this feature.
- [ ] Extension Feature 4: Support verification of total correctness of while loops. Your syntax may diverge from Viper for this task.
- [ ] Extension Feature 5: Support verification of total correctness of recursive methods. Your syntax may diverge from Viper for this task.
- [ ] Extension Feature 6: Lift the restriction that input parameters of MicroViper methods are read-only. Changing an input inside of a method body should still have no effect outside of that method. (Hint: Notice that you may still wish to refer to the original value of input parameters in pre-and postconditions.)
- [ ] Extension Feature 7: Support global variables in MicroViper, that is, declarations var name:type should be allowed outside of method bodies. Your syntax may diverge from Viper for this task. (Hint: Global variables have consequences for how you deal with method calls.)
- [ ] Extension Feature 8: Feel free to suggest other extension features that you would like to add to your verifier.

## Install and Run the Project

For building the project, you will need to have the following installed:

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

## Project structure & Design decisions

- The `syntax` module defines the Abstract Syntax Tree (AST) for the input language, which also does semantic analysis before returning the AST.
    - It uses [LALRPOP](https://github.com/lalrpop/lalrpop/) for parsing,
    - [miette](https://github.com/zkat/miette) for error reporting.
- `src/main.rs` is the entry point for interacting with the project. Use `cargo run` and pass a list of files to parse and analyze.
    - To parse and analyze all the included examples run
    ```bash
    $ cargo run examples/**/*.vpr
    ```
    - The main function returns [`miette::Result<()>`](https://docs.rs/miette/latest/miette/type.Result.html), which allows the [try operator (`?`)](https://blog.rust-lang.org/2016/11/10/Rust-1.13.html#the--operator) to be used in main and possibly in the rest of the project to get nice error reporting. Read the [miette docs](https://docs.rs/miette/latest/miette/index.html) for more details.

## Feature Tests
### Core Feature 1

### Core Feature 2

### Core Feature 3

## Shared Code
N/A
