{-# OPTIONS --no-qualified-instances #-}
module CF.Compile where

open import Data.Product
open import Data.List hiding (null; [_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad.Possibly
open import Relation.Ternary.Monad.Weakening
open import Relation.Ternary.Data.ReflexiveTransitive

open import CF.Syntax as Src
open import CF.Contexts.Lexical

open import CF.Transform.Hoist
open import CF.Transform.UnCo
open import CF.Transform.Compile.Expressions
open import CF.Transform.Compile.Statements
open import CF.Transform.Compile.ToJVM

open import JVM.Builtins
open import JVM.Types
open import JVM.Contexts
open import JVM.Syntax.Values
open import JVM.Syntax.Instructions
open import JVM.Transform.Noooops
open import JVM.Compiler

module _ {T : Set} where
  open import JVM.Model T public

compile : ∀ {r} → Src.Block r [] → ∃ λ Γ → ε[ ⟪ Γ ∣ [] ↝ [] ⟫ ]
compile bl₁                       with hoist bl₁
... | _ , Possibly.possibly (intros r refl) bl₂  -- The grading of the possibility modality
                                                 -- proves that only the lexical context has been extended
          with unco bl₂
... | bl₃ with execCompiler (compiler [] bl₃)
... | bl₄ with noooop bl₄
... | bl₅ = -, bl₅
