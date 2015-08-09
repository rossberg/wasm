# WASM Interpreter

This repository implements a prototypical reference interpreter for WASM. It is written for clarity and simplicity, _not_ speed (although it should be reasonably fast). Hopefully, it can be useful as a playground for trying out ideas and a device for nailing down the exact semantics. The code is written in a fairly declarative, "speccy" way.

Currently, it can

* *parse* a simple S-expression format,
* *validate* modules defined in it,
* *execute* invocations to functions exported by a module.

The file format is a (very dumb) form of *script* that cannot just define a module, but also specify memory size and batch a sequence of invocations.

The interpreter can also be run as a REPL, allowing to enter pieces of scripts interactively.


## Building

You'll need OCaml. Then simply invoke `make`. You'll get an executable named `wasm`.


## Language

For most part, the language understood by the interpreter is based on Ben's V8 prototype, but I took the liberty to try out a few simplifications and generalisations:

* *Expression Language.* There is no distinction between statements and expressions, everything is an expression. Some have an empty return type. Consequently, there is no need for a comma operator or ternary operator.

* *Multiple Values.* Functions can return multiple values. These can be destructured with a dedicated expression. They can also be returned from a caller (e.g. for tail-calls). Parameters and results are treated fully symmetrically.

* *Simple Loops*. Like in Ben's prototype, there is only one sort of loop, the infinite one, which is terminated by a `break`. In such a language, a `continue` statement actually is completely redundant, because it can already be expressed by a Break from the loop's *body*. So I dropped `continue`.

* *Break with Arguments.* In the spirit of a true expression language, `break` can carry arguments, which then become the result of the labelled expression it cuts to.

* *Switch with Explicit Fallthru*. By default, a switch arm is well-behaved in that it does *not* fall through to the next case. However, it can be marked as fallthru explicitly.


## Core Language vs External Language

The implementation tries to separate the concern of what is the language from what is its external encoding. In that spirit, the actual AST is made regular and minimal, while certain abbreviations are considered "syntactic sugar" of an external representation optimised for compactness.

For example, `if` always has an else-branch in the AST, but in the external format an else-less conditional is allowed as an abbreviation for one with `nop`. Simlarly, blocks can sometimes be left implicit in the S-expression format. Furthermore, fallthru is a flag on each `switch` arm in the AST, but an explicit "opcode" in the external form.

Here, the external format is S-expressions, but similar considerations would apply to a binary encoding. That is, there would be codes for certain abbreviations, but these are just a coding concern.


## Internal Syntax

The core language is defined in `syntax.ml`, and looks as follows:

```
type var = int

type expr =
  | Nop                                 (* do nothing
  | Block of expr list                  (* execute in sequence
  | If of expr * expr * expr            (* conditional
  | Loop of expr                        (* infinite loop
  | Label of expr                       (* labelled expression
  | Break of int * expr list            (* break to n-th surrounding label
  | Switch of expr * arm list * expr    (* switch, latter expr is default
  | Call of var * expr list             (* call function
  | Dispatch of var * expr * expr list  (* call function through table
  | Return of expr list                 (* return 0 to many value
  | Destruct of var list * expr         (* destructure multi-value into locals
  | GetLocal of var                     (* read local variable
  | SetLocal of var * expr              (* write local variable
  | GetGlobal of var                    (* read glboal variable
  | SetGlobal of var * expr             (* write global variable
  | GetMemory of memop * expr           (* read memory address
  | SetMemory of memop * expr * expr    (* write memory address
  | Const of value                      (* constant
  | Unary of unop * expr                (* unary arithmetic operator
  | Binary of binop * expr * expr       (* binary arithmetic operator
  | Compare of relop * expr * expr      (* arithmetic comparison
  | Convert of cvt * expr               (* conversion

and arm = {value : int32; expr : expr; fallthru : bool}
```

See the code for more details on the auxiliary types. It also contains ASTs for functions and modules.


## External Syntax

The S-expression syntax is defined in `parser.mly`, the opcodes in `lexer.mll`. Here is an overview of the grammar of types, expressions, functions, and modules:

```
type: i32 | i64 | f32 | f64
memtype: <type> | i8 | i16

num: <int> | <float>
var: <int>

unop:  neg | abs | not | ...
binop: add | sub | mul | ...
relop: eq | neq | lt | ...
memop: (near|far)(unaligned)?(s|u)?

expr:
  ( nop )
  ( block <expr>+ )
  ( if <expr> <expr> <expr> )
  ( if <expr> <expr> )             // = (if <expr> <expr> (nop))
  ( loop <expr>* )                 // = (loop (block <expr>*))
  ( label <expr>* )                // = (label (block <expr>*))
  ( break <var> <expr>* )
  ( break )                        // = (break 0)
  ( switch <expr> <case>* <expr> )
  ( call <var> <expr>* )
  ( dispatch <var> <expr> <expr>* )
  ( return <expr>* )
  ( destruct <var>* <expr> )
  ( getlocal <var> )
  ( setlocal <var> <expr> )
  ( getglobal <var> )
  ( setglobal <var> <expr> )
  ( get<memop>.<memtype> <expr> )
  ( set<memop>.<memtype> <expr> <expr> )
  ( const.<type> <num> )
  ( <unop>.<type> <expr> )
  ( <binop>.<type> <expr> <expr> )
  ( <relop>.<type> <expr> <expr> )
  ( convert(s|u)?.<type>.<type> <expr> )
  ( cast.<type>.<type> <expr> )

case:
  ( case <int> <expr>* fallthru? )  // = (case <int> (block <expr>*) fallthru?)
  ( case <int> )                    // = (case <int> (nop) fallthru)

module: ( module <func>* <global>* <export>* <table>* )
func:   ( func <param>* <result>* <local>* <expr>* )
param:  ( param <type>* )
result: ( result <type>* )
local:  ( local <type>* )
global: ( global <type>* )
export: ( export <var>* )
table:  ( table <var>* )
```

Here, productions marked with respective comments are abbreviation forms for equivalent expansions.


## Scripts

In order to be able to check and run modules, the S-expression format supports a very, very simple notion of "script", with commands as follows:

```
script: <cmd>*

cmd:
  ( memory int )            // allocate memory
  <module>                  // define, validate, and initialize module
  <func>                    // = (module <func> (export 0))
  ( invoke <var> <expr>* )  // invoke export and print result
  ( invoke <expr>* )        // = (invoke 0 <expr>*)
```

A `memory` command allocates fresh memory, and is needed before defining a module. Invocation is only possible after a module has been defined.

The interpreter also supports a "dry" mode (flag `-d`), in which modules are only validated. In this mode, `memory` and `invoke` commands are ignored (and not needed).


## Implementation

The most interesting pieces are probably the validator (`check.ml`) and the evaluator (`eval.ml`), which are written to look as much like a "specification" as possible. Hopefully, the code is fairly self-explanatory, if you have a passing familiarity with functional programming.

A couple of random notes:

* The validator works by passing down the *expected* type (or rather, a list thereof, because of multi-values), and checking each expression against that. The expected type is always determined by context. An expected empty list of types can be matched by any result, corresponding to implicit dropping of unused values (e.g. in a block).

* Evaluation of control transfer (`break` and `return`) is implemented using local exceptions as "labels". While these are allocated dynamically in the code and addressed via a stack, that is merely to simplify the code. In reality, these would be static jumps.

  (Alternatively, we could move to modelling the semantics more abstractly with explicit completion records, but making that look nice would require an evaluation monad.)


## What Next?

* TODOs: unsigned and accurate float32 arithmetics.

* Tests.

* Compilation to JS.

* Binary input format?
