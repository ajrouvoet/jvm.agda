module JVM.Model {ℓ} (T : Set ℓ) where

open import Level hiding (Lift)
open import Data.Product
open import Data.List
open import Data.List.Extra

open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import Relation.Ternary.Construct.Empty T public
open import Relation.Ternary.Construct.Duplicate T

open import Relation.Ternary.Construct.Bag empty-rel as D public using ()
  renaming
    ( bags to disjoint-bags
    ; bags-isSemigroup to disjoint-isSemigroup
    ; bags-isMonoid to disjoint-isMonoid
    ; bags-isCommutative to disjoint-isCommutative
    )
open import Relation.Ternary.Construct.Bag duplicate as O public using ()
  renaming
    ( bags to union-bags
    ; bags-isSemigroup to union-isSemigroup
    ; bags-isMonoid to union-isMonoid
    ; bags-isCommutative to union-isCommutative
    )

open Rel₃ D.bags using () public
  renaming (_∙_≣_ to _⊕_≣_; _⊙_ to _⊕_; _─⊙_ to _─⊕_)
open Rel₃ O.bags using () public
  renaming (_∙_≣_ to _⊗_≣_; _⊙_ to _⊗_; _─⊙_ to _─⊗_)

open import Relation.Ternary.Construct.Bag.Properties
open CrossSplittable {{div₁ = duplicate}} {{empty-rel}} (λ _ ())

open import Relation.Ternary.Construct.Exchange xsplit (uncrossover (unxcross λ ())) public
  renaming (Account to Intf)

-- Creating binders is pure in the model by means of hiding
binder : ∀ τ → ε[ Up (Just τ) ⊙ Down (Just τ) ]
binder τ = (↑ PEq.refl ∙⟨ ex ε-sub xs-xs≡ε ∙-idˡ ∙-idˡ ⟩ ↓ PEq.refl)
