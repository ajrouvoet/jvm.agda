{- Noop removal transformation on bytecode -}
module JVM.Defaults.Transform.Noooops where

open import Data.Product
open import Function using (case_of_)
open import Data.List
open import Relation.Unary
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import JVM.Types
open import JVM.Model StackTy; open Syntax
open import JVM.Defaults.Syntax.Instructions

open import Relation.Ternary.Data.ReflexiveTransitive {{intf-rel}}

open IsEquivalence {{...}} using (sym)
open import Data.Maybe using (just; nothing; Maybe)

is-noop : ∀ {Φ} → (i : ⟨ τ ∣ ψ₁ ⇒ ψ₂ ⟩ Φ) → Maybe (ψ₁ ≡ ψ₂ × Φ ≡ [])
is-noop noop = just (refl , refl)
is-noop _    = nothing

noooop : ∀[ ⟪ τ ∣ ψ₁ ⇒ ψ₂ ⟫ ⇒ ⟪ τ ∣ ψ₁ ⇒ ψ₂ ⟫ ]
noooop nil = nil

-- (1) not labeled
noooop (cons (instr (↓ i) ∙⟨ σ ⟩ is)) =
  case (is-noop i) of λ where
    nothing              → cons (instr (↓ i) ∙⟨ σ ⟩ noooop is)
    (just (refl , refl)) → (coe {{star-respects}} (∙-id⁻ˡ σ) (noooop is))

-- (2) is labeled
noooop (cons (li@(labeled (l ∙⟨ σ₀ ⟩ ↓ i)) ∙⟨ σ ⟩ is)) =
  case (is-noop i) of λ where
    nothing              → cons (li ∙⟨ σ ⟩ noooop is)
    (just (refl , refl)) → label-start noop l ⟨ coe {{∙-respects-≈ˡ}} (sym (∙-id⁻ʳ σ₀)) σ ⟩ (noooop is)
