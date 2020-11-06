{-# OPTIONS --safe #-}
open import Data.List as List hiding ([_])

module JVM.Compiler.Monad (T : Set) (⟨_⇒_⟩ : T → T → List T → Set) (nop : ∀ {τ} → ⟨ τ ⇒ τ ⟩ []) where

open import Level
open import Function using (_∘_)
open import Data.Product hiding (_<*>_)
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad
open import Relation.Ternary.Data.ReflexiveTransitive as Star
open import Relation.Ternary.Data.Bigplus as Bigplus

private
  variable
    τ₁ τ₂ τ : T

open import JVM.Model T; open Syntax
open import JVM.Syntax.Bytecode T ⟨_⇒_⟩

open import Relation.Ternary.Monad.Writer intf-rel
open WriterMonad (starMonoid {R = Code}) renaming
  ( Writer to Compiler
  ; execWriter to execCompiler)
  public

-- Output a single, unlabeled instruction
code : ∀[ ⟨ τ₁ ⇒ τ₂ ⟩ ⇒ Down⁻ (Compiler τ₁ τ₂ Emp) ] 
code i = tell Star.[ instr (↓ i) ]

-- We can label the start of a compiler computation
attachTo : ∀ {P} → ∀[ Up (One τ₁) ⇒ Compiler τ₁ τ₂ P ─✴ Compiler τ₁ τ₂ P ]
attachTo l = censor (label-start nop ⦇ Bigplus.[ l ] ⦈)

attach : ∀[ Up (One τ₁) ⇒ Compiler τ₁ τ₁ Emp ]
attach l = attachTo l ⟨ ∙-idʳ ⟩ return refl

-- Creating binders is pure in the model by means of hiding
freshLabel : ∀ {ψ} → ε[ Compiler τ τ (Up (Own List.[ ψ ]) ✴ Down (Own List.[ ψ ])) ]
freshLabel = return balance
