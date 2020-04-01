{-# OPTIONS --safe #-}
module JVM.Model {ℓ} (T : Set ℓ) where

open import Level hiding (Lift)
open import Data.Product
open import Data.Unit
open import Data.List

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import Relation.Ternary.Construct.Empty T public
open import Relation.Ternary.Construct.Duplicate T public

open import Data.List.Relation.Binary.Permutation.Propositional
  using ()
  renaming (_↭_ to _≈_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++-isMonoid)

instance ++-monoid-instance = ++-isMonoid

module Disjoint where
  open import Relation.Ternary.Construct.Bag empty-rel tt public
  open IsPartialSemigroup bags-isSemigroup public
  open IsPartialMonoid bags-isMonoid public
  open IsCommutative bags-isCommutative public

module Overlap where
  open import Relation.Ternary.Construct.Bag duplicate tt public
  open IsPartialSemigroup bags-isSemigroup public
  open IsPartialMonoid bags-isMonoid public
  open IsCommutative bags-isCommutative  public
  open IsTotal bags-isTotal public

open Rel₃ Disjoint.bags using ()
  renaming (_∙_≣_ to _⊕_≣_; _✴_ to _⊕_; _─✴_ to _─⊕_; _∙⟨_⟩_ to _⊕⟨_⟩_) public
open Rel₃ Overlap.bags using ()
  renaming (_∙_≣_ to _⊗_≣_; _✴_ to _⊗_; _─✴_ to _─⊗_; _∙⟨_⟩_ to _⊗⟨_⟩_) public

open import Relation.Ternary.Construct.Bag.Properties
open CrossSplittable {{div₁ = duplicate}} {{empty-rel}} (λ _ ())

abstract
  private
    m₁ =  Disjoint.bags-isMonoid
    m₂ = Overlap.bags-isMonoid
    p₁ = Disjoint.bags-isPositive
    p₂ = Overlap.bags-isPositive
    c₁ = Disjoint.bags-isCommutative
    c₂ = Overlap.bags-isCommutative
    i  = Overlap.bags-isIntuitionistic
    x  = xsplit
    ux = (uncrossover (unxcross λ ()))

  open import Relation.Ternary.Construct.Exchange
    {{m₁}} {{m₂}} {{p₁}} {{p₂}} {{c₁}} {{c₂}} {{i}}
    {{Disjoint.bags-isTotal}}
    {{Overlap.bags-isTotal}}
    {{++-isMonoid}}
    x ux
    public
    renaming
      (Account to Intf
      ; _≈_ to _≈intf≈_
      ; exchange-rel to intf-rel
      ; exchange-emptiness to intf-emptiness
      ; exchange-isSemigroup to intf-isSemigroup
      ; exchange-isCommutative to intf-isCommutative
      ; exchange-isMonoid to intf-isMonoid
      ; exchange-intuitive-down to intf-isIntuitive
      ; exchange-isTotal to intf-isTotal)

module Syntax where
  open Rel₃ intf-rel public
  open Emptiness          intf-emptiness     public
  open IsPartialSemigroup intf-isSemigroup   public
  open IsPartialMonoid    intf-isMonoid      public
  open IsCommutative      intf-isCommutative public
  open CommutativeSemigroupOps {{intf-isSemigroup}} {{intf-isCommutative}} public
  open IsIntuitionistic   intf-isIntuitive   public

open Syntax

-- Creating binders is pure in the model by means of hiding
binder : ∀ τ → ε[ Up (Just τ) ✴ Down (Just τ) ]
binder τ = ↑ refl ∙⟨ ex ε-sub xs-xs≡ε Disjoint.∙-idˡ Overlap.∙-idˡ ⟩ ↓ refl
