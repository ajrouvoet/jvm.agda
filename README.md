# Intrinsically-Typed Compilation with Nameless Labeles
> Or "One PRSA To Bind Them All"

To avoid compilation errors it is desired to verify that a compiler is
_type correct_---i.e., given well-typed source code, it always outputs
well-typed target code. We present an approach to verify type correctness of a
compiler _intrinsically_ by implementing it as a function in the
dependently-typed programming language Agda.

A key challenge in implementing a compiler intrinsically is the
representation of labels in bytecode. Because label names are global, bytecode
typing appears inherently a non-compositional, whole-program property. The
individual operations of the compiler do not preserve this property.

We address this problem using a new _nameless_ and typed global label binding.
Our key idea is to use _linearity_ to ensure that all labels are bound exactly
once.  We develop a linear, dependently-typed, shallowly embedded language in
Agda, based on separation logic.  And implement intrinsically-typed operations
on bytecode, culminating in an intrinsically-typed compiler for a language with
structured control-flow.

## Type-checking the code

This repository relies heavily on Agda's instance search to get overloaded syntax
for the separation logic connectives and primitives. Unfortunately stable
Agda contains a performance bug related to these. The repository thus requires
fixes that are only in Agda master (to be released in 2.6.2).

To install, follow the instructions from the official documentation 
[here](https://agda.readthedocs.io/en/v2.6.1/getting-started/installation.html#installation-of-the-development-version).
The lastest commit that we tested was 552987aa0119.

A good place to start exploring the codebase is [Everything.agda](./src.Everything.agda),
which links to all the moving parts and relates them to the paper.

## Compiling the examples

Lacking a frontend, we include two example programs embedded in Agda.
These programs can be compiled with `make examples`. The binaries that output
print the resulting bytecode will be output in `./_build/bin`.
The compilation makes use of the haskell tool [stack](https://docs.haskellstack.org/en/stable/README/),
which needs to be installed prior.

