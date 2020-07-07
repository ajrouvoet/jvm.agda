{-# OPTIONS --safe --no-qualified-instances #-}
module CF.Contexts.WithToplevel where

open import Level
open import Data.Unit
open import Data.Product
open import Data.String using (String)
open import Data.List
open import Data.List.Properties as LP
open import Data.List.Relation.Binary.Sublist.Propositional.Properties
open import Relation.Unary hiding (_⊢_; _⊆_; _∈_)

open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

open import CF.Types

open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Sublist.Propositional

open import JVM.Model TopLevelDecl public hiding (module Syntax)
open Overlap hiding (∙-disjointᵣᵣ; ∙-parallel)
open Overlap using (^_) public

Ctx : Set
Ctx = Globals × List Ty

_⍮_ : Ctx → List Ty → Ctx
(X , Γ) ⍮ Δ = X , Γ ++ Δ

variable
  K K₁ K₂ K₃ K₄ : Ctx
  Δ Δ₁ Δ₂ : List Ty

module _ where

  open import Relation.Ternary.Construct.Product as Pr

  instance list-empty : ∀ {a} {A : Set a} → Emptiness {A = List A} []
  list-empty = record {}

  open import Relation.Ternary.Construct.List.Overlapping Ty

  _ctx≈_ : Ctx → Ctx → Set
  _ctx≈_ = Pr._≈_ {{↭-isEquivalence}} {{isEquivalence}}

  Lex = List Ty

  Vars : Lex → Pred Ctx 0ℓ
  Vars Γ = Π₂ (Own Γ)
  
  Global : TopLevelDecl → Pred Ctx 0ℓ
  Global tl = Π₁ (One tl)

  Closed : ∀ {ℓ} → Pred Ctx ℓ → Pred Globals ℓ
  Closed P X = P (X , ε)

  data _∼[_]_ : Ctx → Lex → Ctx → Set where
    intros : ∀ {Γ X Δ Δ′ Γ′} → Δ′ ⊆ Δ → Γ′ ≡ Γ ++ Δ′ → (X , Γ) ∼[ Δ ] (X , Γ′)
    

  open import Relation.Ternary.Monad.Possibly
  open Possibly _∼[_]_
    public
    using (possibly; ◇; module ◇-GradedMonad; module ◇-Zip; _∼_; pack)
    renaming
      ( ◇[_] to _⊢_)

  ∼-all : K ∼[ Δ ] (K ⍮ Δ)
  ∼-all = intros ⊆-refl refl

  ∼-none : K ∼[ Δ ] K
  ∼-none {X , Γ} {Δ} =
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
  ∼-fp (_ , intros ext refl) (_ , σ₂ , σ₁) = (-, σ₂ , ∙-disjointᵣᵣ σ₁) , _ , intros ⊆-refl refl

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
      ∼-pull δ (σ₂ , σ₁) (intros p refl) (intros q refl) with _ , δ′ , r ← Ov.⊆-⊗ p q δ =
        -, (σ₂ , ∙-parallel σ₁ δ′) , intros r refl

  open ◇-Zip ∼-pull public renaming (◇-zip to ⊢-zip)

  binders : ∀ {Γ} → ε[ Γ ⊢ Vars Γ ]
  binders = Possibly.possibly ∼-all (snd refl)

module CoDeBruijn where

  open import Relation.Ternary.Construct.Product as Pr

  Var : Ty → Pred Ctx 0ℓ
  Var a = Vars [ a ]

  pattern vars = snd refl

  Fun : FunTy → Pred Ctx 0ℓ
  Fun f = Global (fun f)

  pattern fn = fst refl

module DeBruijn where
  open import Data.List.Membership.Propositional

  Var : Ty → Pred Ctx 0ℓ
  Var a (X , Γ) = a ∈ Γ

  Fun : FunTy → Pred Ctx 0ℓ
  Fun t (X , Γ) = (fun t) ∈ X

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

  instance ctx-isPositive : IsPositiveWithZero 0ℓ _ctx≈_ ctx-rel unit
  ctx-isPositive = ×-isPositive-w/0

  instance ctx-isCommutative : IsCommutative ctx-rel
  ctx-isCommutative = ×-isCommutative
