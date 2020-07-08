{-# OPTIONS --no-qualified-instances #-}
{- Noop removal transformation on bytecode -}
module JVM.Transform.Noooops where

open import Data.Product
open import Data.Sum
open import Function using (case_of_)
open import Data.List
open import Relation.Unary hiding (Empty)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax hiding (_∣_)

open import JVM.Types
open import JVM.Model StackTy
open import JVM.Syntax.Instructions

open import Relation.Ternary.Data.ReflexiveTransitive {{intf-rel}}

open IsEquivalence {{...}} using (sym)
open import Data.Maybe using (just; nothing; Maybe)

is-noop : ∀[ ⟨ 𝑭 ∣ ψ₁ ↝ ψ₂ ⟩ ⇒ (Empty (ψ₁ ≡ ψ₂) ∪ U) ]
is-noop noop = inj₁ (emp refl)
is-noop _    = inj₂ _

noooop : ∀[ ⟪ 𝑭 ∣ ψ₁ ↝ ψ₂ ⟫ ⇒ ⟪ 𝑭 ∣ ψ₁ ↝ ψ₂ ⟫ ]
noooop nil = nil

-- (1) not labeled
noooop (cons (instr (↓ i) ∙⟨ σ ⟩ is)) =
  case (is-noop i) of λ where
    (inj₂ _)          → instr (↓ i) ▹⟨ σ ⟩ noooop is
    (inj₁ (emp refl)) → coe (∙-id⁻ˡ σ) (noooop is)

-- (2) is labeled
noooop (cons (li@(labeled (l ∙⟨ σ₀ ⟩ ↓ i)) ∙⟨ σ ⟩ is)) =
  case (is-noop i) of λ where
    (inj₂ _)          → cons (li ∙⟨ σ ⟩ noooop is)
    (inj₁ (emp refl)) → label-start noop l ⟨ coe {{∙-respects-≈ˡ}} (≈-sym (∙-id⁻ʳ σ₀)) σ ⟩ (noooop is)
