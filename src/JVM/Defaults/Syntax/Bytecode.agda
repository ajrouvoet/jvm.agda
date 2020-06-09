{-# OPTIONS --safe --no-qualified-instances #-}
-- Bytecode; i.e., instruction sequences; 
-- agnostic about the exact instructions, but opiniated about labels
open import Data.List hiding (concat)

module JVM.Defaults.Syntax.Bytecode {ℓ} (T : Set ℓ) (I : T → T → List T → Set ℓ) where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Relation.Unary hiding (_∈_; Empty)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Data.ReflexiveTransitive as Star
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Data.Bigstar
open import Relation.Ternary.Data.IndexedMonoid

open import Data.Sum
open import Data.Product
 
open import JVM.Model T
open Disjoint using (bags; bags-isMonoid; bags-isSemigroup; bags-isCommutative; empty-unique)

open import JVM.Defaults.Syntax.Labeling T public

data Code : T → T → Pred Intf ℓ where
  labeled : ∀ {τ₁ τ₂} → ∀[ Up (Labeling τ₁) ✴ Down (I τ₁ τ₂) ⇒ Code τ₁ τ₂ ]
  instr   : ∀ {τ₁ τ₂} → ∀[ Down (I τ₁ τ₂) ⇒ Code τ₁ τ₂ ]

getInstr : ∀ {τ₁ τ₂} → ∀[ Code τ₁ τ₂ ⇒ Down (I τ₁ τ₂) ✴ Code τ₁ τ₂ ]
getInstr c@(labeled (l ∙⟨ σ ⟩ i@(↓ _))) =
  let (i ∙⟨ σ ⟩ l∙i) = ✴-swap (✴-assocₗ (l ∙⟨ σ ⟩ copy i))
  in i ∙⟨ σ ⟩ labeled l∙i
getInstr (instr i@(↓ _)) = i ∙⟨ ∙-copy i ⟩ (instr i)

label : ∀ {τ₁ τ₂} → ∀[ Up (Labeling τ₁) ⇒ Code τ₁ τ₂ ─✴ Code τ₁ τ₂ ]
label l ⟨ σ ⟩ instr i   = labeled (l ∙⟨ σ ⟩ i)
label l ⟨ σ ⟩ labeled (l₂∙i) with ✴-assocₗ (l ∙⟨ σ ⟩ l₂∙i)
... | l₁∙l₂ ∙⟨ σ′ ⟩ i with upMap (↑ (✴-curry (arrow concat))) ⟨ ∙-idˡ ⟩ zipUp l₁∙l₂
... | ls = labeled (ls ∙⟨ σ′ ⟩ i)

⟪_↝_⟫ : T → T → Pred Intf ℓ
⟪ τ₁ ↝ τ₂ ⟫ = Star Code τ₁ τ₂

⟪_↝_⟫+ : T → T → Pred Intf ℓ
⟪ τ₁ ↝ τ₂ ⟫+ = Plus Code τ₁ τ₂

⟪_↜_⟫ : T → T → Pred Intf ℓ
⟪ τ₂ ↜ τ₁ ⟫ = Star (flip Code) τ₁ τ₂
  where open import Function using (flip)

module _ (nop : ∀ {τ} → I τ τ []) where

  label-start : ∀ {τ₁ τ₂} → ∀[ Up (Labeling τ₁) ⇒ ⟪ τ₁ ↝ τ₂ ⟫ ─✴ ⟪ τ₁ ↝ τ₂ ⟫ ]
  label-start l = mappend Star.[ labeled (l ∙⟨ ∙-idʳ ⟩ ↓ nop) ]
