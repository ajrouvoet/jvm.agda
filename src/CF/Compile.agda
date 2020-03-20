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
open import CF.Transform.Hoist
open import CF.Compile.Expressions
open import CF.Compile.Statements

open import JVM.Types
open import JVM.Contexts
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions
open import JVM.Defaults.Transform.Noooops

-- Given a closed block, run the entire compiler pipeline:
-- 1. Hoist local variables
-- 2. Compile to bytecode
-- 3. Remove redundant noops
compile : Src.Block r [] → ∃ λ Γ → ε[ ⟪ Γ ∣ [] ⇒ [] ⟫ ]
compile bl with
  _ , Possibly.possibly _ bl' ← hoist bl | compiler [] (bl' ⇈ ∙-idʳ)
... | bc ∙⟨ σ ⟩ refl with bc' ← noooop bc = -, coe (∙-id⁻ʳ σ) bc'
