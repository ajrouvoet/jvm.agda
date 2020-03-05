module JVM.Model {ℓ} (T : Set ℓ) where

open import Level hiding (Lift)
open import Data.Product
open import Data.List
open import Data.List.Extra

open import Relation.Unary hiding (_∈_)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
open IsEquivalence {{...}}

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Respect.Propositional

private
  Labels = List T
  variable
    u₁ u₂ u₃ d₁ d₂ d₃ u d : Labels

open import Data.Unit
open import Relation.Ternary.Construct.Empty T
open import Relation.Ternary.Construct.Duplicate T

open import Relation.Ternary.Construct.Bag empty-rel as D
open import Relation.Ternary.Construct.Bag duplicate as O

open Rel₃ D.bags using () public
  renaming (_∙_≣_ to _⊕_≣_; _⊙_ to _⊕_; _─⊙_ to _─⊕_)
open Rel₃ O.bags using () public
  renaming (_∙_≣_ to _⊗_≣_; _⊙_ to _⊗_; _─⊙_ to _─⊗_)

open import Relation.Ternary.Construct.Bag.Properties
open CrossSplittable {{div₁ = duplicate}} {{empty-rel}} (λ _ ())

open import Relation.Ternary.Construct.Exchange xsplit (uncrossover (unxcross λ ())) public

-- Creating binders is pure in the model by means of hiding
binder : ∀ τ → ε[ Up (Just τ) ⊙ Down (Just τ) ]
binder τ = (↑ PEq.refl ∙⟨ ex ε-sub xs-xs≡ε ∙-idˡ ∙-idˡ ⟩ ↓ PEq.refl)
