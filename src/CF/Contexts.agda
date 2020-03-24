{-# OPTIONS --safe #-}
module CF.Contexts where

open import Level
open import Data.Unit
open import Data.Product
open import Data.String using (String)
open import Data.List
open import Data.List.Properties as LP
open import Relation.Unary hiding (_⊢_; _⊆_; _∈_)

open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Construct.Product as Pr

open import CF.Types

open import Data.List.Relation.Binary.Permutation.Propositional

record FunTy : Set where
  constructor _⟶_
  field
    argtys : List Ty
    retty  : Ty

data ToplevelTy : Set where
  fun : FunTy → ToplevelTy

TopLevelDecl = String × ToplevelTy

variable
  𝑓 𝑔 ℎ : String

Globals : Set
Globals = List TopLevelDecl

open import JVM.Model TopLevelDecl public

Lex = List Ty

abstract

  Ctx : Set
  Ctx = Lex × Globals

  variable
    K K₁ K₂ K₃ K₄ : Ctx
    Δ Δ₁ Δ₂ : List Ty

  _⍮_ : Ctx → List Ty → Ctx
  (Γ , X) ⍮ Δ = (Δ ++ Γ , X)

  module DJList where
    open import Relation.Ternary.Construct.List.Disjoint Ty public

  module OVList where
    open import Relation.Ternary.Construct.List.Overlapping Ty public

  instance ctx-rel : Rel₃ Ctx
  ctx-rel = ×-rel {{OVList.overlap-rel}} {{Overlap.bags}}

  private
    unit : Ctx
    unit = [] , []

  instance ctx-emptiness : Emptiness {A = Ctx} unit
  ctx-emptiness = record {}

  _ctx≈_ : Ctx → Ctx → Set
  _ctx≈_ = Pr._≈_ {{isEquivalence}} {{↭-isEquivalence}}

  instance ctx-isSemigroup : IsPartialSemigroup _ctx≈_ ctx-rel
  ctx-isSemigroup = ×-isSemigroup

  instance ctx-isMonoid : IsPartialMonoid _ctx≈_ ctx-rel unit
  ctx-isMonoid = ×-isPartialMonoid

  instance ctx-isPositive : IsPositive 0ℓ _ctx≈_ ctx-rel unit
  ctx-isPositive = ×-isPositive

  instance ctx-isCommutative : IsCommutative ctx-rel
  ctx-isCommutative = ×-isCommutative

  Vars : Lex → Pred Ctx 0ℓ
  Vars Γ = Π₁ (Exactly Γ)
  
  Global : TopLevelDecl → Pred Ctx 0ℓ
  Global tl = Π₂ (Just tl)

  data _∼[_]_ : Ctx → Lex → Ctx → Set where
    intros : ∀ {Γ χ Δ Δ′} → Δ′ DJList.⊆ Δ → (Γ , χ) ∼[ Δ ] (Δ′ ++ Γ , χ)

  open import Relation.Ternary.Monad.Possibly
  open Possibly _∼[_]_
    public
    using (◇; module ◇-Zip; module ◇-Monad; _∼_; pack)
    renaming
      ( ◇[_] to _⊢_)

  ∼-all : K ∼[ Δ ] (K ⍮ Δ)
  ∼-all = intros DJList.⊆-refl

  ∼-none : K ∼[ Δ ] K
  ∼-none {Γ , X} {Δ} = intros (-, ∙-idˡ)

  ∼-trans : K₁ ∼ K₂ → K₂ ∼ K₃ → K₁ ∼ K₃
  ∼-trans {K₁} (Δ₁ , intros {Δ′ = Δ₁′} p) (Δ₂ , intros {Δ′ = Δ₂′} q) =
    -, subst (K₁ ∼[ _ ]_) (cong (_, _) (LP.++-assoc Δ₂′ Δ₁′ _)) (intros DJList.⊆-refl)

  ∼-isPreorder : IsPreorder _≡_ _∼_
  IsPreorder.isEquivalence ∼-isPreorder = isEquivalence
  IsPreorder.reflexive ∼-isPreorder refl = -, ∼-all
  IsPreorder.trans ∼-isPreorder = ∼-trans

  -- frame preserving
  ∼-fp : K₁ ∼ K₂ → (di₁ : K₃ ◆ K₁) → ∃ λ (di₂ : K₃ ◆ K₂) → whole di₁ ∼ whole di₂
  ∼-fp (_ , intros ext) (_ , σ₁ , σ₂) = (-, ∙-∙ᵣₗ σ₁ , σ₂) , _ , intros DJList.⊆-refl

  open ◇-Monad ∼-isPreorder ∼-fp public
    renaming (◇-⤇ to ⊢-⤇)

  module _ where
    open import Relation.Ternary.Construct.List.Overlapping Ty as Ov
    abstract
      ∼-pull : Δ₁ Ov.⊗ Δ₂ ≣ Δ
             → K₁ ∙ K₃ ≣ K
             → K₁ ∼[ Δ₁ ] K₂
             → K₃ ∼[ Δ₂ ] K₄
             → ∃ λ K' → K₂ ∙ K₄ ≣ K' × K ∼[ Δ ] K'
      ∼-pull δ (σ₁ , σ₂) (intros p) (intros q) with _ , δ′ , r ← Ov.⊆-⊗ p q δ = -, (∙-parallel δ′ σ₁ , σ₂) , intros r

  open ◇-Zip ∼-pull public renaming (◇-zip to ⊢-zip)

  binders : ∀ {Γ} → ε[ Γ ⊢ Vars Γ ]
  binders = Possibly.possibly ∼-all (fst (subst ｛ _ ｝ (sym (LP.++-identityʳ _)) refl))

module _ where

  Var : Ty → Pred Ctx 0ℓ
  Var a = Vars [ a ]

  Fun : String → FunTy → Pred Ctx 0ℓ
  Fun n f = Global (n , fun f)

  abstract
    Closed : ∀ {ℓ} → Pred Ctx ℓ → Pred Globals ℓ
    Closed P X = P (ε , X)
