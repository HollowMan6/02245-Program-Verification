# (A) Building a Verifier

> Group: 2
> - s233511: Songlin Jiang
> - s233508: Jawad Zaheer

An automated verification tool in Rust for MicroViper – a subset of the language supported by the Viper verification infrastructure. It includes a parser and static analyzer for the input format _MicroViper_ (see example below), with nice error reporting. The code is for [project A](https://pv.cmath.eu/projects/construction.html) of the course [02245 — Program Verification](http://courses.compute.dtu.dk/02245/).

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
- [X] Extension Feature 1: Support partial correctness verification of multiple (and possibly mutally recursive) methods.
- [X] Extension Feature 2: Support user-defined functions that can be defined by providing a function body, or pre- and postconditions, or both. (Hint: Recall that function bodies and calls are expressions, that is, function calls may appear in specifications.)
- [X] Extension Feature 3: Use efficient weakest preconditions in your MicroViper verifier. Provide sufficiently large examples to demonstrate support of this feature.
- [X] Extension Feature 4 (with no guarantee of completeness): Support verification of total correctness of while loops. Your syntax may diverge from Viper for this task.
- [X] Extension Feature 5 (with no guarantee of completeness): Support verification of total correctness of recursive methods. Your syntax may diverge from Viper for this task.
- [X] Extension Feature 6 (with no guarantee of completeness): Lift the restriction that input parameters of MicroViper methods are read-only. Changing an input inside of a method body should still have no effect outside of that method. (Hint: Notice that you may still wish to refer to the original value of input parameters in pre-and postconditions.)
- [ ] Extension Feature 7: Support global variables in MicroViper, that is, declarations var name:type should be allowed outside of method bodies. Your syntax may diverge from Viper for this task. (Hint: Global variables have consequences for how you deal with method calls.)
- [X] Extension Feature 8: Support reporting all assertion errors in one file at the same time (which is different than viper since it can only report the assertion errors one at a time). We also support issuing warnings when there exist contradictory assumptions, and remove that branch of weakest preconditions afterwards, to improve the efficiency.

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

### Get started with verification

Use `cargo run` and pass a list of files to parse and analyze.

- To parse and analyze all the included examples run

```bash
$ cargo run examples/**/*.vpr
```

If the file fails the satisfiability check, an error will be thrown, e.g.:

```log
 × An error occurred while checking examples/01-using-viper/04-triple.vpr:
   ╭─[1:1]
 1 │ method triple(x: Int) returns (r: Int)
 2 │     ensures r == 3 * x
   ·             ─────┬────
   ·                  ╰──  + This assertion is unsatisfiable
 3 │ {
   ╰────
  help: Fix this and try again!
```

## Project structure & Design decisions

### Structure
#### `syntax` module

The `syntax` module defines the Abstract Syntax Tree (AST) for the input language, which also does semantic analysis before returning the AST.

- It uses [LALRPOP](https://github.com/lalrpop/lalrpop/) for parsing,
- [miette](https://github.com/zkat/miette) for error reporting.

#### `src/main.rs`

It serves as the entry point for interacting with the project. It is responsible for converting the micro Viper Abstract Syntax Tree (AST) into the Z3 AST and performing verification using standard weakest preconditions and checking satisfiability.

##### `Variable` enum

The `Variable` enum represents different types of variables used in the Z3 context. It can be either a boolean variable (`Bool`) or an integer variable (`Int`), both of which are associated with their respective Z3 representations. This enum is designed to abstract the different types of variables used in the Z3 context, making it easier to handle variables with different data types. The associated Z3 representations allow for seamless integration with the Z3 solver.

###### Variants

- `Bool(z3::ast::Bool<'a>)`: Represents a boolean variable with its Z3 boolean representation.
- `Int(z3::ast::Int<'a>)`: Represents an integer variable with its Z3 integer representation.

##### `Value` enum

The `Value` enum represents different types of values that can be encountered during the parsing and evaluation process. It can be either a boolean value (`Bool`), an integer value (`Int`), or a variable (`Var`) along with its associated Z3 representation. This enum is designed to abstract different types of values encountered during parsing and evaluation, allowing for seamless handling of values with different data types. The associated Z3 representation (in the case of a variable) enables integration with the Z3 solver.

###### Variants

- `Bool(bool)`: Represents a boolean value.
- `Int(i64)`: Represents an integer value.
- `Var(Variable<'a>)`: Represents a variable along with its associated Z3 representation.

##### `Wrong` struct

The `Wrong` struct represents an error or incorrect state encountered during the parsing or evaluation process. It contains a descriptive error message (`msg`) along with the span (`(usize, usize)`) indicating the location or range where the error occurred. This struct is designed to encapsulate errors encountered during parsing or evaluation, allowing for informative error messages along with location information. It helps in providing detailed context about the incorrect state or error.

###### Fields

- `msg: String`: Descriptive error message providing information about the incorrect state or error.
- `span: (usize, usize)`: Tuple representing the start and end positions (as `usize`) where the error occurred.

### Design

We don't introduce explicit AST types for every translation step, since we believe it will slow down the parsing speed. Instead, we parse the micro-viper AST in two rounds:
- For the first round, collect `inputs`, `outputs`, `ensures`, `requires` of all methods and functions. Also we collect the body for functions. We store all those things separately into a hashmap, using the method/function name as the key.
- For the second round, we do the actual convertion to the Z3 API.

We have a global storage for all the variables instances used by z3, and the global counter used to keep track of the newest fresh variables. During the method assignment or function call parsing, we will append the method/function name together with `-` to all variable names that belongs to the calling method/function (in `parse_type`). Whenever we need a fresh variable, we will increase the counter by one and store the new instance into the variables hashmap (`fresh_variable`, `peak_body` for while loop).

We use the efficient weakest preconditions for verification as suggested in the course slides. We use a 2D vector to store the collected assumptions. All the ensures/requires/expressions will be converted into assumptions or assertions during parsing in the second round. We also handle function calls, method assignments (in `pre_call`), if, while etc. according to the best method presented in the course slide. For each assumption, we push it to all the layers of assumptions vector (in `add_assumption`). We will merge the assumptions when we do the choice, and ensures that we have the same fresh variable. (in `post_choice_branch`).

When we encounter assertions, we will iterate through assumptions layers, for each layer, we concatenate each assumption with "and", the result implies the asserted expression, and we then apply the not operation. If the result is unsat, we will pass the assertion. (in `assert`)

For extension feature 8, We will execute `assert false` after we finish `add_assumption`, if it's not report any error, then that assumptions branch is in a contradiction and we just remove that branch.

We will report the while loop total correctness error when condition is "true" or something like "a == a", also when assert condition is ok before havoc, and variables in condition expression never gets reassigned in body (we collect the variables in while condition with `peek_expr`, and the variables that get assigned with `peek_body`).

We will also report the recursive total correctness error when the methods are directly called in the body, or in both of the choice branches. (As of our extension feature 8, it's not necessary to check if both of the branch will be a valid path here).

## Feature Tests

Set the DEBUG flag in main.rs to true, execute `cargo run tests/*.vpr`, then you can see the assumptions for each verification step. All the error reports are compared with carbon backend of viper to make sure they report the same assumption errors, for our own-supported features, we just check manually. Generated assumptions are also checked manually to ensure that it works correctly.

### Core Feature 1 & 2
[tests/core.vpr](tests/core.vpr)

### Core Feature 3
[examples/03-bonus/annotsum.vpr](examples/03-bonus/annotsum.vpr)

### Extension Feature 1
[examples/01-using-viper/09-maxsum.vpr](examples/01-using-viper/09-maxsum.vpr)

### Extension Feature 2
[tests/extension_feature_2.vpr](tests/extension_feature_2.vpr)

### Extension Feature 3
We have tested all the viper files in [examples](examples) folder and it all works correctly. 

### Extension Feature 4
[tests/extension_feature_4.vpr](tests/extension_feature_4.vpr)

Supposed error reported:
```
  × An error occurred while checking tests/extension_feature_4.vpr:
    ╭─[14:1]
 14 │ 
 15 │   while (i > n) {
    ·          ──┬──
    ·            ╰── while condition is always true and value never got changed (total correctness)
 16 │     assert res == n * (n + 1) / 2
    ╰────
  help: Fix this and try again!
```

```
  × An error occurred while checking tests/extension_feature_4.vpr:
    ╭─[18:1]
 18 │ 
 19 │   while (i == i) {
    ·          ───┬──
    ·             ╰── while condition is always true (total correctness)
 20 │     i := i + 1
    ╰────
  help: Fix this and try again!
```

### Extension Feature 5
[tests/extension_feature_5.vpr](tests/extension_feature_5.vpr)

Supposed error reported:
```
  × An error occurred while checking tests/extension_feature_5.vpr:
   ╭─[7:1]
 7 │   }
 8 │   y := wrong1(x)
   ·        ───┬──
   ·           ╰── Warning: Calling method now will likely cause infinite stack (not totally correct)
 9 │   y := 2 * x + 1
   ╰────
  help: Fix this and try again!
```

```
  × An error occurred while checking tests/extension_feature_5.vpr:
    ╭─[18:1]
 18 │     y := 12
 19 │     y := wrong2(x)
    ·          ───┬──
    ·             ╰── Warning: Calling method now will likely cause infinite stack (not totally correct)
 20 │   }
    ╰────
  help: Fix this and try again!
```
### Extension Feature 6
Since we use the name as the prefix when we call methods/functions, this should be OK, but we didn't modify the syntax module to lift the method to test this feature.

### Extension Feature 8
[tests/extension_feature_8.vpr](tests/extension_feature_8.vpr)

Supposed error reported:
```
  × An error occurred while checking tests/extension_feature_8.vpr:
   ╭─[5:1]
 5 │     assume x == 5
 6 │     if (x == 5) {
   ·         ───┬──
   ·            ╰── Warning: This assumption causes contradiction in one of the branch, dropping that branch now
 7 │         y := 6
   ╰────
  help: Fix this and try again!
```

```
  × An error occurred while checking tests/extension_feature_8.vpr:
    ╭─[15:1]
 15 │     requires x > 0
 16 │     requires x < 0
    ·              ──┬──
    ·                ╰── Warning: Contradict requires condition, all assertions will not report error now
 17 │     ensures y > x
    ╰────
  help: Fix this and try again!
```

## Shared Code

N/A
