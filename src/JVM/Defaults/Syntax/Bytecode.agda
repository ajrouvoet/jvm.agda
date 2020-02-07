-- Bytecode; i.e., instruction sequences; 
-- agnostic about the exact instructions, but opiniated about labels
open import Relation.Binary using (Rel)
open import Data.List

module JVM.Defaults.Syntax.Bytecode {ℓ} (T : Set ℓ) (I : T → T → List T → Set ℓ) where

open import Level
open import Relation.Unary
open import Relation.Ternary.Data.ReflexiveTransitive public
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List.Relation.Binary.Permutation.Inductive hiding (swap)

Labels  = List T

variable
  τ τ₁ τ₂ : T

module _
  {{labels : Rel₃ Labels}}
  {e u} {_≈_ : Rel Labels e}
  {{_ : IsPartialMonoid _≈_ labels u}}
  {{_ : IsCrosssplittable _≈_ labels}}
  {{_ : IsPositive _≈_ labels u}}
  {{_ : IsCommutative labels}}
  where

  open import Relation.Ternary.Construct.Exchange {A = Labels} _≈_ as Exchange
    renaming (Account to Intf; _≈_ to Intf[_≈_]) public

  data Code : T → T → Pred Intf ℓ where
    label : ∀[ Up (Just τ)    ⇒ Code τ  τ  ]
    instr : ∀[ Down (I τ₁ τ₂) ⇒ Code τ₁ τ₂ ]

  ⟪_⇒_⟫ : T → T → Pred Intf ℓ
  ⟪ τ₁ ⇒ τ₂ ⟫ = Star Code τ₁ τ₂

  ⟪_⇐_⟫ : T → T → Pred Intf ℓ
  ⟪ τ₂ ⇐ τ₁ ⟫ = Star (flip Code) τ₁ τ₂
    where open import Function using (flip)

  record Zipper (τ τ′ : T) (Φ : Intf) : Set ℓ where
    constructor zipped 
    field
      {τₗ τᵣ} : T
      code    : (⟪ τₗ ⇐ τ ⟫ ⊙ Down (I τ τ′) ⊙ ⟪ τ′ ⇒ τᵣ ⟫) Φ

  {-# TERMINATING #-}
  focus-next : ∀ {τₗ τᵣ} → ∀[ ⟪ τₗ ⇐ τ ⟫ ⇒ ⟪ τ ⇒ τᵣ ⟫ ─⊙ (U ∪ (⋃[ τ′ ∶ _ ] Zipper τ τ′)) ]
  focus-next b ⟨ σ ⟩ nil    = inj₁ tt
  focus-next b ⟨ σ ⟩ (cons f@(label _ ∙⟨ _ ⟩ _)) with ⊙-assocₗ (b ∙⟨ σ ⟩ f)
  ... | (b' ∙⟨ σ₃ ⟩ f') = focus-next (cons (⊙-swap b')) ⟨ σ₃ ⟩ f'
  focus-next b ⟨ σ ⟩ (instr i ▹⟨ σ₂ ⟩ f) =
    inj₂ (-, zipped (b ∙⟨ σ ⟩ (i ∙⟨ σ₂ ⟩ f)))

  moveᵣ : ∀[ Zipper τ₁ τ₂ ⇒ (Zipper τ₁ τ₂ ∪ (⋃[ τ₃ ∶ _ ] Zipper τ₂ τ₃)) ]
  moveᵣ (zipped z) with ⊙-assocₗ z
  ... | ((b ∙⟨ σ₁ ⟩ i) ∙⟨ σ₂ ⟩ n) with focus-next (instr i ▹⟨ ∙-comm σ₁ ⟩ b) ⟨ σ₂ ⟩ n
  ... | inj₁ _  = inj₁ (zipped z)
  ... | inj₂ z′ = inj₂ z′
