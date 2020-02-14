* JVM Code, two ways

The module `Defaults`does type-safe compilation of Middleweight Java,
assuming that variable declarations and register allocations come with default values.
The main focus of this work is showing that the co-de-bruijn representation of labels in Bytecode
using the exchange PRSA solves the problems of a (hypothetical) de-bruijn encoding.

```agda
module JVM.Defaults.Readme where

import JVM.Defaults.Syntax.Bytecode
```
