{-# OPTIONS --safe #-}
module JVM.Model {ℓ} (T : Set ℓ) where

open import Level hiding (Lift)
open import Data.Product
open import Data.Unit
open import Data.List
open import Data.List.Extra

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import Relation.Ternary.Construct.Empty T public
open import Relation.Ternary.Construct.Duplicate T

module Disjoint where
  open import Relation.Ternary.Construct.Bag empty-rel tt public
  open IsPartialSemigroup bags-isSemigroup public
  open IsPartialMonoid bags-isMonoid public

module Overlap where
  open import Relation.Ternary.Construct.Bag duplicate tt public
  open IsPartialSemigroup bags-isSemigroup public
  open IsPartialMonoid bags-isMonoid public

open Rel₃ Disjoint.bags using ()
  renaming (_∙_≣_ to _⊕_≣_; _⊙_ to _⊕_; _─⊙_ to _─⊕_)
open Rel₃ Overlap.bags using ()
  renaming (_∙_≣_ to _⊗_≣_; _⊙_ to _⊗_; _─⊙_ to _─⊗_)

open import Relation.Ternary.Construct.Bag.Properties
open CrossSplittable {{div₁ = duplicate}} {{empty-rel}} (λ _ ())

open import Relation.Ternary.Construct.Exchange
  {{Disjoint.bags}}
  {{Overlap.bags}}
  {{Disjoint.bags-isMonoid}}
  {{Overlap.bags-isMonoid}}
  {{Disjoint.bags-isPositive}}
  {{Overlap.bags-isPositive}}
  {{Disjoint.bags-isCommutative}}
  {{Overlap.bags-isCommutative}}
  xsplit (uncrossover (unxcross λ ())) public
  renaming
    (Account to Intf
    ; exchange-rel to intf-rel
    ; exchange-emptiness to intf-emptiness
    ; exchange-isSemigroup to intf-isSemigroup
    ; exchange-isCommutative to intf-isCommutative
    ; exchange-isMonoid to intf-isMonoid)

module Syntax where
  open Rel₃ intf-rel public
  open Emptiness          intf-emptiness     public
  open IsPartialSemigroup intf-isSemigroup   public
  open IsPartialMonoid    intf-isMonoid      public
  open IsCommutative      intf-isCommutative public
  open CommutativeSemigroupOps {{intf-isSemigroup}} {{intf-isCommutative}} public

open Syntax

-- Creating binders is pure in the model by means of hiding
binder : ∀ τ → ε[ Up (Just τ) ⊙ Down (Just τ) ]
binder τ = ↑ refl ∙⟨ ex ε-sub xs-xs≡ε Disjoint.∙-idˡ Overlap.∙-idˡ ⟩ ↓ refl
