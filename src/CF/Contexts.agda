{-# OPTIONS --safe --no-qualified-instances #-}
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

open import CF.Types

open import Data.List.Relation.Binary.Permutation.Propositional

open import JVM.Model TopLevelDecl public hiding (module Syntax)
open Overlap hiding (∙-∙ᵣₗ; ∙-parallel)
open Overlap using (^_) public

module _ where

  open import Relation.Ternary.Construct.Product as Pr

  module DJList where
    open import Relation.Ternary.Construct.List.Disjoint Ty public

  instance list-empty : ∀ {a} {A : Set a} → Emptiness {A = List A} []
  list-empty = record {}

  open import Relation.Ternary.Construct.List.Overlapping Ty

  _ctx≈_ : Ctx → Ctx → Set
  _ctx≈_ = Pr._≈_ {{↭-isEquivalence}} {{isEquivalence}}

  Vars : Lex → Pred Ctx 0ℓ
  Vars Γ = Π₂ (Exactly Γ)
  
  Global : TopLevelDecl → Pred Ctx 0ℓ
  Global tl = Π₁ (Just tl)

  data _∼[_]_ : Ctx → Lex → Ctx → Set where
    intros : ∀ {Γ X Δ Δ′} → Δ′ DJList.⊆ Δ → (X , Γ) ∼[ Δ ] (X , Δ′ ++ Γ)

  open import Relation.Ternary.Monad.Possibly
  open Possibly _∼[_]_
    public
    using (◇; module ◇-Zip; _∼_; pack)
    renaming
      ( ◇[_] to _⊢_)

  ∼-all : K ∼[ Δ ] (K ⍮ Δ)
  ∼-all = intros DJList.⊆-refl

  ∼-none : K ∼[ Δ ] K
  ∼-none {Γ , X} {Δ} = intros DJList.⊆-min

  ∼-trans : K₁ ∼ K₂ → K₂ ∼ K₃ → K₁ ∼ K₃
  ∼-trans {K₁} (Δ₁ , intros {Δ′ = Δ₁′} p) (Δ₂ , intros {Δ′ = Δ₂′} q) =
    -, subst (K₁ ∼[ _ ]_) (cong (_ ,_) (LP.++-assoc Δ₂′ Δ₁′ _)) (intros DJList.⊆-refl)

  ∼-isPreorder : IsPreorder _≡_ _∼_
  IsPreorder.isEquivalence ∼-isPreorder = isEquivalence
  IsPreorder.reflexive ∼-isPreorder refl = -, ∼-all
  IsPreorder.trans ∼-isPreorder = ∼-trans

  -- frame preserving
  ∼-fp : K₁ ∼ K₂ → (di₁ : K₃ ◆ K₁) → ∃ λ (di₂ : K₃ ◆ K₂) → whole di₁ ∼ whole di₂
  ∼-fp (_ , intros ext) (_ , σ₂ , σ₁) = (-, σ₂ , ∙-∙ᵣₗ σ₁) , _ , intros DJList.⊆-refl

  open ◇-Monad _∼[_]_ ∼-isPreorder ∼-fp public

  module _ where
    open import Relation.Ternary.Construct.List.Overlapping Ty as Ov
    abstract
      ∼-pull : Δ₁ Ov.⊗ Δ₂ ≣ Δ
             → K₁ ∙ K₃ ≣ K
             → K₁ ∼[ Δ₁ ] K₂
             → K₃ ∼[ Δ₂ ] K₄
             → ∃ λ K' → K₂ ∙ K₄ ≣ K' × K ∼[ Δ ] K'
      ∼-pull δ (σ₂ , σ₁) (intros p) (intros q) with _ , δ′ , r ← Ov.⊆-⊗ p q δ = -, (σ₂ , ∙-parallel δ′ σ₁) , intros r

  open ◇-Zip ∼-pull public renaming (◇-zip to ⊢-zip)

  binders : ∀ {Γ} → ε[ Γ ⊢ Vars Γ ]
  binders = Possibly.possibly ∼-all (snd (subst ｛ _ ｝ (sym (LP.++-identityʳ _)) refl))

module CoDeBruijn where

  open import Relation.Ternary.Construct.Product as Pr

  Var : Ty → Pred Ctx 0ℓ
  Var a = Vars [ a ]

  pattern vars = snd refl

  Fun : String → FunTy → Pred Ctx 0ℓ
  Fun n f = Global (n , fun f)

  pattern fn = fst refl

  Closed : ∀ {ℓ} → Pred Ctx ℓ → Pred Globals ℓ
  Closed P X = P (X , ε)

module DeBruijn where
  open import Data.List.Membership.Propositional

  Var : Ty → Pred Ctx 0ℓ
  Var a (X , Γ) = a ∈ Γ

  Fun : String → FunTy → Pred Ctx 0ℓ
  Fun n t (X , Γ) = (n , fun t) ∈ X

open CoDeBruijn public

{- We redefine the instances to force instanc resolution to happen here rather than in the dependants -}
module _ where

  open import Relation.Ternary.Construct.Product as Pr
  open import Relation.Ternary.Construct.List.Overlapping Ty

  instance ctx-rel : Rel₃ Ctx
  ctx-rel = ×-rel {{Overlap.bags}} {{overlap-rel}}

  private
    unit : Ctx
    unit = [] , []

  instance ctx-emptiness : Emptiness {A = Ctx} unit
  ctx-emptiness = record {}

  instance ctx-isSemigroup : IsPartialSemigroup _ctx≈_ ctx-rel
  ctx-isSemigroup = ×-isSemigroup

  instance ctx-isMonoid : IsPartialMonoid _ctx≈_ ctx-rel unit
  ctx-isMonoid = ×-isPartialMonoid

  instance ctx-isPositive : IsPositive 0ℓ _ctx≈_ ctx-rel unit
  ctx-isPositive = ×-isPositive

  instance ctx-isCommutative : IsCommutative ctx-rel
  ctx-isCommutative = ×-isCommutative
