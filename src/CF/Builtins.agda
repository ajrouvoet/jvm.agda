{-# OPTIONS --safe --no-qualified-instances #-}
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

open import CF.Contexts.WithToplevel
open import CF.Types
open import CF.Transform.Compile.ToJVM

open import JVM.Types
open import JVM.Compiler
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions
open import JVM.Builtins

open import Relation.Ternary.Data.ReflexiveTransitive hiding ([_])

-- Signatures of builtin functions of CF
print : TopLevelDecl
print = fun ("print" ∶ [ int ] ⟶ void)

builtins : List TopLevelDecl
builtins = print
         ∷ []

-- Compilation of builtins to typed bytecode
⟦builtins⟧ : All (λ where (fun (name ∶ as ⟶ b)) → ⟪ jre , ⟦ as ⟧ ∣ [] ⇒ ⟦ b ⟧ ∷ [] ⟫ ε) builtins
⟦builtins⟧ = execCompiler ⟦print⟧
          ∷ []

  where

    ⟦print⟧ : Compiler (jre , _) [] [ _ ] Emp _
    ⟦print⟧ = do
      code (load (here refl))
      code (getstatic (here refl))
      code (invokevirtual (there (here refl)))
      code (push (bool true))
