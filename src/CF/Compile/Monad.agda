open import Data.List hiding ([_])

module CF.Compile.Monad (T : Set) (⟨_⇒_⟩ : T → T → List T → Set) (nop : ∀ {τ} → ⟨ τ ⇒ τ ⟩ []) where

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

instance compiler-monad : Monad T Compiler
Monad.return compiler-monad = nil ∙⟨ ∙-idˡ ⟩_
Monad.bind compiler-monad f ⟨ σ ⟩ (is ∙⟨ σ₂ ⟩ px) =
  let
    _ , σ₃ , σ₄   = ∙-assocₗ σ (∙-comm σ₂)
    js ∙⟨ σ₃ ⟩ qx = f ⟨ σ₃ ⟩ px
    _ , σ₅ , σ₆   = ∙-assocₗ (∙-comm σ₄) σ₃ in (Star.append is ⟨ σ₅ ⟩ js) ∙⟨ σ₆ ⟩ qx

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

open Monad compiler-monad public
open Bind     {{monad = compiler-monad}} {{ ⊙-respect-≈ }} public
open Strength {{monad = compiler-monad}} public
