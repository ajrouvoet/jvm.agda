{-# OPTIONS --safe --no-qualified-instances #-}
module CF.Contexts.Lexical where

open import Level
open import Data.Unit
open import Data.Product
open import Data.String using (String)
open import Data.List
open import Data.List.Properties as LP
open import Data.List.Relation.Binary.Sublist.Propositional.Properties

open import Relation.Unary hiding (_⊢_; _⊆_; _∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

open import CF.Types

open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Sublist.Propositional

Ctx : Set
Ctx = List Ty

_⍮_ : Ctx → List Ty → Ctx
Γ ⍮ Δ = Γ ++ Δ

variable
  K K₁ K₂ K₃ K₄ : Ctx
  Δ Δ₁ Δ₂ : List Ty

module CoDeBruijn where

  open import Relation.Ternary.Construct.List.Overlapping Ty public

  instance list-empty : ∀ {a} {A : Set a} → Emptiness {A = List A} []
  list-empty = record {}

  Vars : Ctx → Pred Ctx 0ℓ
  Vars Γ = Own Γ
  
  Closed : ∀ {ℓ} → Pred Ctx ℓ → Set ℓ
  Closed P = P ε

  data _∼[_]_ : Ctx → Ctx → Ctx → Set where
    intros : ∀ {Γ Δ Δ′ Γ′} → Δ′ ⊆ Δ → Γ′ ≡ Γ ++ Δ′ → Γ ∼[ Δ ] Γ′

  open import Relation.Ternary.Monad.Possibly
  open Possibly _∼[_]_
    public
    using (possibly; ◇; module ◇-GradedMonad; module ◇-Zip; _∼_; pack)
    renaming
      ( ◇[_] to _⊢_)

  ∼-all : K ∼[ Δ ] (K ⍮ Δ)
  ∼-all = intros ⊆-refl refl

  ∼-none : K ∼[ Δ ] K
  ∼-none {Γ} {Δ} =
    intros (minimum Δ) (sym (++-identityʳ Γ))

  ∼-refl : K ∼[ ε ] K
  ∼-refl = ∼-none

  ∼-trans : K₁ ∼ K₂ → K₂ ∼ K₃ → K₁ ∼ K₃
  ∼-trans {K₁} (Δ₁ , intros {Δ′ = Δ₁′} p refl) (Δ₂ , intros {Δ′ = Δ₂′} q refl) =
    -, intros ⊆-refl (LP.++-assoc _ Δ₁′ Δ₂′)

  ∼-isPreorder : IsPreorder _≡_ _∼_
  IsPreorder.isEquivalence ∼-isPreorder = isEquivalence
  IsPreorder.reflexive ∼-isPreorder refl = -, ∼-refl
  IsPreorder.trans ∼-isPreorder = ∼-trans

  -- frame preserving
  ∼-fp : K₁ ∼ K₂ → (di₁ : K₃ ◆ K₁) → ∃ λ (di₂ : K₃ ◆ K₂) → whole di₁ ∼ whole di₂
  ∼-fp (_ , intros ext refl) (_ , σ₁) = (-, ∙-disjointᵣᵣ σ₁) , _ , intros ⊆-refl refl

  open ◇-Monad _∼[_]_ ∼-isPreorder ∼-fp public

  -- specialized version of graded join because I'm lazy
  ∼-goin : ∀ {p} {P : Pred Ctx p} → ∀[ Δ₁ ⊢ (Δ₂ ⊢ P) ⇒ (Δ₁ ++ Δ₂) ⊢ P ]
  ∼-goin (Possibly.possibly
    (intros {Γ} {Δ′ = Δ₁} r₁ refl)
    (Possibly.possibly (intros r₂ refl) px)) =
      possibly (intros (++⁺ r₁ r₂) (++-assoc Γ Δ₁ _ )) px

  module _ where
    open import Relation.Ternary.Construct.List.Overlapping Ty as Ov
    abstract
      ∼-pull : Δ₁ Ov.⊗ Δ₂ ≣ Δ
             → K₁ ∙ K₃ ≣ K
             → K₁ ∼[ Δ₁ ] K₂
             → K₃ ∼[ Δ₂ ] K₄
             → ∃ λ K' → K₂ ∙ K₄ ≣ K' × K ∼[ Δ ] K'
      ∼-pull δ σ₁ (intros p refl) (intros q refl) with _ , δ′ , r ← Ov.⊆-⊗ p q δ =
        -, ∙-parallel σ₁ δ′ , intros r refl

  open ◇-Zip ∼-pull public renaming (◇-zip to ⊢-zip)

  binders : ∀ {Γ} → ε[ Γ ⊢ Vars Γ ]
  binders = Possibly.possibly ∼-all refl

  Var : Ty → Pred Ctx 0ℓ
  Var a = Vars [ a ]

  pattern vars = refl

module DeBruijn where
  open import Data.List.Membership.Propositional

  Var : Ty → Pred Ctx 0ℓ
  Var a Γ = a ∈ Γ

  _⊢_ : ∀ {ℓ} → List Ty → Pt Ctx ℓ
  Δ ⊢ P = λ Γ → P (Γ ⍮ Δ)

  -- ◇′ : Pt Ctx 0ℓ
  -- ◇′ P = ⋃[ as ∶ _ ] as ⊢ P 

open CoDeBruijn public
