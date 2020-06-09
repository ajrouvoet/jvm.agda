module JVM.Model.Properties where

open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Data.Product hiding (map)

open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Construct.Bag.Properties
open import Function

module _ {p t} {T : Set t} {P : Pred _ p} where

  open import JVM.Model (List T)
  open import Data.List.Relation.Unary.All

  -- If you know the split and what is bubbling up from the left and right parts,
  -- then you know what bubbles up from the composite.
  source : ∀ {Φ₁ : Intf} → Φ₁ ∙ Φ₂ ≣ Φ → All P (up Φ₁) → All P (up Φ₂) → All P (up Φ)
  source (ex (sub x₁ x₂) (sub x₃ x₄) x₅ x₆) ks ls = {!!}

  -- If you know the split and what is bubbling up from the left and flowing down the composite,
  -- then you know what flows down the right part.
  sinkᵣ : ∀ {Φ₁ : Intf} → Φ₁ ∙ Φ₂ ≣ Φ → All P (up Φ₁) → All P (down Φ) → All P (down Φ₂)
  sinkᵣ (ex (sub x₁ x₂) (sub x₃ x₄) x₅ x₆) ks ls = {!!}

  -- The same, but different.
  sinkₗ : ∀ {Φ₁ Φ₂ Φ : Intf} → Φ₁ ∙ Φ₂ ≣ Φ → All P (up Φ₂) → All P (down Φ) → All P (down Φ₁)
  sinkₗ σ ups downs = sinkᵣ (∙-comm σ) ups downs

-- {- Mapping along any injection yields a model morphism -}
-- module _ {a b} {A : Set a} {B : Set b} (𝑚 : A ↣ B) where

--   open Injection 𝑚

--   private
--     ⟦_⟧ = λ a → f a
--     j   = map ⟦_⟧

--   open import JVM.Model A as L
--   open import JVM.Model B as R
--   import Relation.Ternary.Construct.Duplicate.Properties as D
--   import Relation.Ternary.Construct.Empty.Properties as E
--   module OMM = MonoidMorphism (bagMap (D.f-morphism 𝑚))
--   module DMM = MonoidMorphism (bagMap (E.⊥-morphism ⟦_⟧))
--   import Relation.Ternary.Construct.Bag.Overlapping as O
--   import Relation.Ternary.Construct.Bag.Disjoint as D

--   private

--     sub-lemma⁺ : ∀ {xs ys u d} → xs L.- ys ≣ (u L.⇅ d) → j xs R.- j ys ≣ (j u R.⇅ j d)
--     sub-lemma⁺ (sub x x₁) = R.sub (DMM.j-∙ x) (OMM.j-∙ x₁)

--     sub-lemma⁻ : ∀ {xs ys u d} → j xs R.- j ys ≣ (u R.⇅ d) →
--                ∃₂ λ u' d' → xs L.- ys ≣ (u' L.⇅ d') × u ≡ j u' × d ≡ j d'
--     sub-lemma⁻ (sub x y)
--       with _ , x' , refl , refl ← D.map-inv _ ⟦_⟧ x
--          | _ , y' , refl , eq   ← O.map-inv _ ⟦_⟧ y
--          with refl ← map-injective 𝑚 eq
--          = -, -, (L.sub x' y' , refl , refl)

--   ⟦⟧-morphism : SemigroupMorphism L.intf-isSemigroup R.intf-isSemigroup
--   SemigroupMorphism.j ⟦⟧-morphism (e ⇅ d)       = (j e) R.⇅ (j d)
--   SemigroupMorphism.jcong ⟦⟧-morphism (ρ₁ , ρ₂) = map⁺ ⟦_⟧ ρ₁ , map⁺ ⟦_⟧ ρ₂
--   SemigroupMorphism.j-∙ ⟦⟧-morphism (ex x x₁ σ₁ σ₂)  =
--     R.ex (sub-lemma⁺ x) (sub-lemma⁺ x₁) (DMM.j-∙ σ₁) (OMM.j-∙ σ₂)
--   SemigroupMorphism.j-∙⁻ ⟦⟧-morphism (ex x x₁ σ₁ σ₂) with sub-lemma⁻ x
--   ... | _ , _ , y  , refl , refl with sub-lemma⁻ x₁
--   ... | _ , _ , y₁ , refl , refl with _ , τ₁ , refl ← DMM.j-∙⁻ σ₁ | _ , τ₂ , refl ← OMM.j-∙⁻ σ₂
--      = -, L.ex y y₁ τ₁ τ₂ , refl
