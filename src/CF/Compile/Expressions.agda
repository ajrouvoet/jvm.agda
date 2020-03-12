module CF.Compile.Expressions where

open import Level
open import Data.Unit
open import Data.Product
open import Data.List hiding (null; [_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import CF.Transform.Hoist

open import JVM.Types
open import JVM.Contexts
open import JVM.Model StackTy; open Syntax
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions

module _ where
  open import Relation.Ternary.Monad {{ctx-rel}}
  open import Relation.Ternary.Monad.Weakening {{_}} {{ctx-commutative}} {{ctx-monoid}} public
  open Bind {{ctx-monoid}} {{⇑-monad {0ℓ} }} {{IsPartialSemigroup.⊙-respect-≈ ctx-semigroup}} using () renaming (_>>=_ to _⇑->>=_) public

module _ Γ where
  open import CF.Compile.Monad StackTy ⟨ Γ ∣_⇒_⟩ using (Compiler) public

module _ {Γ} where
  open import CF.Compile.Monad StackTy ⟨ Γ ∣_⇒_⟩ hiding (Compiler) public


  {-# TERMINATING #-}
  compileₑ : ∀ {ψ : StackTy} → (Exp a ⇑) Γ → Compiler Γ ψ (a ∷ ψ) Emp ([] ⇅ [])

  compileₑ (unit ⇈ wk) = do
    tell (↓ (push unit))

  compileₑ (null ⇈ wk) = do
    tell (↓ (push null))

  compileₑ (num x ⇈ wk) = do
    tell (↓ (push (num x)))

  compileₑ (var x ⇈ wk) = do
    tell (↓ (load (x ⇈ wk)))

  compileₑ (iop f e₁∙e₂ ⇈ wk) = do
    let e₁ = (e₁∙e₂  ⇈ wk) ⇑->>= π₁
    let e₂ = (e₁∙e₂  ⇈ wk) ⇑->>= (π₂)

    refl ← compileₑ e₁
    refl ← compileₑ e₂
    tell (↓ (bop f))

  compileₑ (ref e ⇈ wk) = do
    refl ← compileₑ (e  ⇈ wk)
    tell (↓ new)

  compileₑ (deref e ⇈ wk) = do
    refl ← compileₑ (e ⇈ wk)
    tell (↓ read)
