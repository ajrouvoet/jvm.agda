module Everything where
-- The development can almost entirely be type-checked using --safe,
-- We mark modules that use the TERMINATING pragma with (**)
-- And one module that uses --rewriting with (*).
-- These are the only modules that Agda does not accept ass --safe.

--  # First we summarize the library we use by Rouvoet et al '20, CPP.
--
--  Our work contributes various improvements to the library.
--  In particular, its generalization relations whose underlying
--  equivalence is not propositional equality.
--  But also various additions to the parts of the library
--  mentioned below.

-- Core defines what a proof-relevant ternary relation (Rel₃).
import Relation.Ternary.Core

-- Structures defines type classes for ternary relations.
-- A PRSA is a commutative monoid and should implement:
--   - IsPartialMonoid <: IsPartialSemigroup
--   - IsCommutative
import Relation.Ternary.Structures

-- The overloaded syntax of separation logic comes from:
import Relation.Ternary.Structures.Syntax

-- Resource aware versions of data types that we use are defined generically
-- in Relation.Ternary.Data:
import Relation.Ternary.Data.Bigstar             -- 'Star' in figure 5 of the paper
import Relation.Ternary.Data.Bigplus             -- 'Plus'
import Relation.Ternary.Data.ReflexiveTransitive -- 'IStar'

-- The computational structures from the library that we use in the paper
import Relation.Ternary.Functor
import Relation.Ternary.Monad




-- # We make the following additions to the library, that we describe in the paper.

-- A generic PRSA for list separation modulo permutations.
-- It is generic in the sense that it is parameterized in a PRSA on its elements.
-- We prove that it is a PRSA, with various additional properties that are
-- crucial for the model construction in the paper.
import Relation.Ternary.Construct.Bag
import Relation.Ternary.Construct.Bag.Properties

-- A generic PRSA Exchange, that generalizes the interface composition relation.
import Relation.Ternary.Construct.Exchange

-- Its construction is generic in 2 PRSAs that obey some properties.
-- These properties are formalized as type-classes on ternary relations
import Relation.Ternary.Structures.Positive
import Relation.Ternary.Structures.Crosssplit

-- We added the writer monad construction described in the paper.
import Relation.Ternary.Monad.Writer




-- # We then formalize the typed language CF, and typed bytecode,
-- and implement the typed compilation backend.

-- The model:
-- The bag separation implements the 'disjoint' and the 'overlapping' context 
-- separation from the paper, depending on how you instantiate it.
-- The instantiation is done in the JVM model construction.
-- Here we also instantiate Exchange to obtain interface composition.
import JVM.Model

-- Syntax of bytecode
import JVM.Types
import JVM.Syntax.Instructions
import JVM.Syntax.Bytecode

-- The Compiler monad
import JVM.Compiler.Monad

-- The source language
import CF.Types
import CF.Syntax           -- co-contextual
import CF.Syntax.Hoisted   -- co-contextual without local variable introductions
import CF.Syntax.DeBruijn  -- contextual

import CF.Transform.Hoist               -- hoisting local variable declarations (**)
import CF.Transform.UnCo                -- contextualizing (**)
import CF.Transform.Compile.Expressions -- compiling expressions
import CF.Transform.Compile.Statements  -- compiling statements
import CF.Transform.Compile.ToJVM       -- typeclass for type translation
import JVM.Transform.Noooops            -- bytecode optimization that removes nops
import JVM.Transform.Assemble           -- bytecode translation to absolute jumps (*)
import JVM.Printer                      -- printer for co-contextual bytecode to Jasmin (not verified) (**)

-- Example compilations.
-- These can be run by first compiling them using `make examples`.
-- The output will be in _build/bin/
import CF.Examples.Ex1 -- (*,**)
import CF.Examples.Ex2 -- (*,**)
