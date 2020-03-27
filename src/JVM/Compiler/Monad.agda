{-# OPTIONS --safe #-}
open import Data.List hiding ([_])

module JVM.Compiler.Monad (T : Set) (⟨_⇒_⟩ : T → T → List T → Set) (nop : ∀ {τ} → ⟨ τ ⇒ τ ⟩ []) where

open import Level
open import Function using (_∘_)
open import Data.Product
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad
open import Relation.Ternary.Data.ReflexiveTransitive as Star
open import Relation.Ternary.Data.Bigstar

private
  variable
    τ₁ τ₂ τ : T

open import JVM.Model T; open Syntax
open import JVM.Defaults.Syntax.Bytecode T ⟨_⇒_⟩

Compiler : T → T → Pt Intf 0ℓ
Compiler ψ₁ ψ₂ P = ⟪ ψ₁ ⇒ ψ₂ ⟫ ⊙ P

instance
  compiler-monad : Monad T Compiler
  Monad.return compiler-monad = nil ∙⟨ ∙-idˡ ⟩_
  Monad._=<<_ compiler-monad f (w ∙⟨ σ ⟩ px) with (w' ∙⟨ σ₂ ⟩ qx) ← f px =
    let _ , σ₃ , σ₄ = ∙-assocₗ σ σ₂ in
    (Star.append w ⟨ σ₃ ⟩ w' ) ∙⟨ σ₄ ⟩ qx

  compiler-strong : Strong T Compiler
  Strong.str compiler-strong qx ⟨ σ ⟩ (w ∙⟨ σ₂ ⟩ px) with _ , σ₃ , σ₄ ← ∙-assocₗ σ (∙-comm σ₂) =
    w ∙⟨ ∙-comm σ₄ ⟩ (qx ∙⟨ σ₃ ⟩ px)

-- Output a single, unlabeled instruction
tell : ∀[ Code τ₁ τ₂ ⇒ Compiler τ₁ τ₂ Emp ] 
tell c = (c ▹⟨ ∙-idʳ ⟩ nil) ∙⟨ ∙-idʳ ⟩ refl

code : ∀[ ⟨ τ₁ ⇒ τ₂ ⟩ ⇒ (Compiler τ₁ τ₂ Emp) ∘ ([] ⇅_) ] 
code i = tell (instr (↓ i))

-- Magically, we can create labels in pairs of positive and negative occurences, in a pure manner.
mklabel : ε[ Compiler τ₁ τ₁ (Up (Just τ) ⊙ Down (Just τ)) ]
mklabel {τ = τ} = return (binder τ)

attach : ∀[ Up (Just τ₁) ⇒ Compiler τ₁ τ₁ Emp ]
attach l = tell (labeled (⦇ [_] l ⦈ ∙⟨ ∙-idʳ ⟩ ↓ nop))

-- We can label the start of a compiler computation
attachTo : ∀ {P} → ∀[ Up (Just τ₁) ⇒ Compiler τ₁ τ₂ P ─⊙ Compiler τ₁ τ₂ P ]
attachTo l ⟨ σ ⟩ c = do
  c ∙⟨ σ ⟩ refl ← attach l &⟨ Compiler _ _ _ # ∙-comm σ ⟩ c
  coe (∙-id⁻ʳ σ) c

execCompiler : ∀ {ψ₁ ψ₂} → ∀[ Compiler ψ₁ ψ₂ Emp ⇒ ⟪ ψ₁ ⇒ ψ₂ ⟫ ]
execCompiler (bc ∙⟨ σ ⟩ refl) = coe (∙-id⁻ʳ σ) bc
