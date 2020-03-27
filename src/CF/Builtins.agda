{-# OPTIONS --no-qualified-instances #-}
module CF.Builtins where

open import Data.Bool
open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All
open import Data.String

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

open import CF.Contexts using (TopLevelDecl; TopLevelTy; _⟶_)
open TopLevelTy
open import CF.Types
open import CF.Syntax
open import CF.Transform.Compile.Expressions

open import JVM.Types
open import JVM.Compiler
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions
open import JVM.Builtins

open import Relation.Ternary.Data.ReflexiveTransitive

-- Signatures of builtin functions of CF
print : TopLevelDecl
print = "print" , fun ([ int ] ⟶ void)

builtins : List TopLevelDecl
builtins = print
         ∷ []

-- Compilation of builtins to typed bytecode
⟦builtins⟧ : All (λ where (name , fun (as ⟶ b)) → ⟪ jre , ⟦ as ⟧ ∣ [] ⇒ ⟦ b ⟧ ∷ [] ⟫ ε) builtins
⟦builtins⟧ = execCompiler ⟦print⟧
          ∷ []

  where

    ⟦print⟧ = do
      code (getstatic (here refl))
      code (load (here refl))
      code (invokevirtual (there (here refl)))
      code (push (bool true))
