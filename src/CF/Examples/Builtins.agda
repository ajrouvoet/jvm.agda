module CF.Examples.Builtins where

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
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions

open import Relation.Ternary.Data.ReflexiveTransitive

-- Assumptions of type-safe compilation
jre : Constantpool
jre = staticref ("java/lang/System"    / "out"     ∶ ref "java/io/PrintStream")
    ∷ virtual   ("java/io/PrintStream" / "println" :⟨ [ int ] ⟩ void)
    ∷ []

-- Signatures of builtin functions of CF
builtins : List TopLevelDecl
builtins = ("print" , fun ([ int ] ⟶ void))
         ∷ []

-- Compilation of builtins to typed bytecode
⟦builtins⟧ : All (λ where (name , fun (as ⟶ b)) → ⟪ jre , ⟦ as ⟧ ∣ [] ⇒ ⟦ b ⟧ ∷ [] ⟫ ε) builtins
⟦builtins⟧ = execCompiler ⟦print⟧
          ∷ []

  where

    ⟦print⟧ : Compiler (jre , [ int ]) [] [ boolean ] Emp ε
    ⟦print⟧ = do
      refl ← code (getstatic (here refl))
      refl ← code (load (here refl))
      refl ← code (invokevirtual (there (here refl)))
      code (push (bool true))
