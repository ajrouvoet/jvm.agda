module JVM.Model.Properties where

open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Morphisms
open import Function

module _ {a b} {A : Set a} {B : Set b} (𝑚 : A ↣ B) where

  open Injection 𝑚

  private
    ⟦_⟧ = λ a → f a
    j   = map ⟦_⟧

  open import JVM.Model A as L
  open import JVM.Model B as R
  import Relation.Ternary.Construct.Bag.Properties as B
  import Relation.Ternary.Construct.Duplicate.Properties as D
  import Relation.Ternary.Construct.Empty.Properties as E
  module OMM = MonoidMorphism (B.bagMap (D.f-morphism 𝑚))
  module DMM = MonoidMorphism (B.bagMap (E.⊥-morphism ⟦_⟧))
  import Relation.Ternary.Construct.Bag.Overlapping as O
  import Relation.Ternary.Construct.Bag.Disjoint as D

  private

    sub-lemma⁺ : ∀ {xs ys u d} → xs L.- ys ≣ (u L.⇅ d) → j xs R.- j ys ≣ (j u R.⇅ j d)
    sub-lemma⁺ (sub x x₁) = R.sub (DMM.j-∙ x) (OMM.j-∙ x₁)

    sub-lemma⁻ : ∀ {xs ys u d} → j xs R.- j ys ≣ (u R.⇅ d) →
               ∃₂ λ u' d' → xs L.- ys ≣ (u' L.⇅ d') × u ≡ j u' × d ≡ j d'
    sub-lemma⁻ (sub x y)
      with _ , x' , refl , refl ← D.map-inv _ ⟦_⟧ x
         | _ , y' , refl , eq   ← O.map-inv _ ⟦_⟧ y
         with refl ← map-injective 𝑚 eq
         = -, -, (L.sub x' y' , refl , refl)

  ⟦⟧-morphism : SemigroupMorphism L.intf-isSemigroup R.intf-isSemigroup
  SemigroupMorphism.j ⟦⟧-morphism (e ⇅ d)       = (j e) R.⇅ (j d)
  SemigroupMorphism.jcong ⟦⟧-morphism (ρ₁ , ρ₂) = map⁺ ⟦_⟧ ρ₁ , map⁺ ⟦_⟧ ρ₂
  SemigroupMorphism.j-∙ ⟦⟧-morphism (ex x x₁ σ₁ σ₂)  =
    R.ex (sub-lemma⁺ x) (sub-lemma⁺ x₁) (DMM.j-∙ σ₁) (OMM.j-∙ σ₂)
  SemigroupMorphism.j-∙⁻ ⟦⟧-morphism (ex x x₁ σ₁ σ₂) with sub-lemma⁻ x
  ... | _ , _ , y  , refl , refl with sub-lemma⁻ x₁
  ... | _ , _ , y₁ , refl , refl with _ , τ₁ , refl ← DMM.j-∙⁻ σ₁ | _ , τ₂ , refl ← OMM.j-∙⁻ σ₂
     = -, L.ex y y₁ τ₁ τ₂ , refl
