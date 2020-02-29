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

open import Relation.Ternary.Construct.List.Overlapping T public
open import Data.Unit

open import Relation.Ternary.Construct.Empty T
open import Relation.Ternary.Construct.List.Disjoint T public hiding (threeway; _∈_)

module _ where

  -- Global binding modularized:
  -- At every part of the tree we have some labels that are exported (up)
  -- and some that are imported (down)
  infixr 1 _↕_
  record Binding : Set ℓ where
    constructor _↕_
    field
      exp : Labels
      imp : Labels

    pair : Labels × Labels
    pair = exp , imp

  open Binding public

  instance binding-emptiness : Emptiness ([] ↕ [])
  binding-emptiness = record {}

  data Down (P : Pred Labels ℓ) : Pred Binding ℓ where
    ↓ : ∀ {x} → P x → Down P ([] ↕ x)

  data Up (P : Pred Labels ℓ) : Pred Binding ℓ where
    ↑ : ∀ {x} → P x → Up P (x ↕ [])

private
  variable
    ud₁ ud₂ ud : Binding

module _ where

  open import Data.List.Relation.Binary.Permutation.Propositional

  {- Subtraction with duplication -}
  data _-_≣_ : Labels → Labels → Binding → Set ℓ where
    sub : ∀ {e e' d' u'} →
          d' ⊕ e  ≣ d → -- disjoint, so that demand is only bound once 
          u' ⊗ e' ≣ u → -- with overlap, so that binders can be reused
          e ↭ e' →
          d - u ≣ (u' ↕ d')

  []-sub : ∀ {xs} → [] - xs ≣ (xs ↕ [])
  []-sub = sub ∙-idˡ ∙-idʳ ↭-refl

  sub-[] : ∀ {xs} → xs - [] ≣ ([] ↕ xs)
  sub-[] = sub ∙-idʳ ∙-idˡ ↭-refl

  []-sub⁻ : ∀ {xs ys zs} → [] - xs ≣ (ys ↕ zs) → ys ≡ xs × zs ≡ []
  []-sub⁻ (sub x x₁ x₂) with ε-split x
  ... | PEq.refl with ↭-[] (↭-sym x₂)
  ... | PEq.refl = ∙-id⁻ʳ x₁ , PEq.refl

  sub-[]⁻ : ∀ {xs ys zs} → xs - [] ≣ (ys ↕ zs) → zs ≡ xs × ys ≡ []
  sub-[]⁻ (sub x x₁ x₂) with ε-split x₁
  ... | PEq.refl with ↭-[] x₂
  ... | PEq.refl = ∙-id⁻ʳ x , PEq.refl

  xs-xs≡ε : ∀ {xs} → xs - xs ≣ ε
  xs-xs≡ε = sub ∙-idˡ ∙-idˡ ↭-refl

  data Binds : Binding → Binding → Binding → Set ℓ where
    -- exchange the rings and bind 'm
    ex : ∀ {u₁' d₁' u₂' d₂'} →
      -- exchange lhs to rhs and vice versa
      d₁ - u₂ ≣ (u₂' ↕ d₂') →
      d₂ - u₁ ≣ (u₁' ↕ d₁') →

      -- add the remaining supply and demand
      u₁' ⊕ u₂' ≣ u →
      d₁' ⊗ d₂' ≣ d →

      Binds (u₁ ↕ d₁) (u₂ ↕ d₂) (u ↕ d)

  instance binding-rel : Rel₃ Binding
  binding-rel = record { _∙_≣_ = Binds }

  instance intuitive : Intuitionistic {A = Binding} binding-rel
  Intuitionistic.Condition intuitive (u ↕ d) = u ≡ [] 
  Intuitionistic.∙-copy intuitive {.[] ↕ xs} ⦃ PEq.refl ⦄ = ex sub-[] sub-[] ∙-idˡ ∙-copy

  instance binding-comm : IsCommutative binding-rel
  IsCommutative.∙-comm binding-comm (ex x₁ x₂ x₃ x₄) = ex x₂ x₁ (∙-comm x₃) (∙-comm x₄)

  postulate binding-semigroupˡ : IsPartialSemigroupˡ _≡_ binding-rel
  -- IsPartialSemigroupˡ.≈-equivalence binding-semigroupˡ = PEq.isEquivalence
  -- -- IsPartialSemigroupˡ.assocᵣ binding-semigroupˡ σ₁ σ₂ = ?

  -- IsPartialSemigroupˡ.assocᵣ binding-semigroupˡ
  --   {a = a↑ ↕ a↓} {b = b↑ ↕ b↓} {ab = ab↑ ↕ ab↓} {c = c↑ ↕ c↓} {abc = abc↑ ↕ abc↓}
  --   (ex (sub {e = e₁} {e' = e₁'} x₈ x₉ x₁₂) (sub {e = e₂} {e₂'} x₁₃ x₁₄ x₁₅) x₁₀ x₁₁) (ex (sub {e = e₃} x x₁ x₄) (sub {e = e₄} x₅ x₆ x₇) x₂ x₃) = {!!}

  -- IsPartialSemigroupˡ.assocᵣ binding-semigroupˡ {abc = [] ↕ imp₁} σ₁ (ex x x₁ x₂ x₃) with ε-split x₂
  -- IsPartialSemigroupˡ.assocᵣ binding-semigroupˡ {b = _} {_} {_} {[] ↕ imp₁} (ex y₁ y₂ y₃ y₄) (ex (sub x x₁ x₄) (sub x₅ x₆ x₇) x₂ x₃) | PEq.refl , PEq.refl
  --   with ∙-id⁻ˡ x₁ | ∙-id⁻ˡ x₆
  -- ... | PEq.refl | PEq.refl = -, ex {!y₁!} {!!} ∙-idˡ {!!} , ex {!!} {!!} {!!} {!!}
  -- IsPartialSemigroupˡ.assocᵣ binding-semigroupˡ {abc = x₄ ∷ exp₁ ↕ imp₁} σ₁ (ex x x₁ x₂ x₃) = {!!}

  instance binding-semigroup : IsPartialSemigroup _≡_ binding-rel
  binding-semigroup = IsPartialSemigroupˡ.semigroupˡ binding-semigroupˡ

  binding-isMonoidˡ : IsPartialMonoidˡ _≡_ binding-rel ([] ↕ [])
  IsPartialMonoidˡ.ε-uniq binding-isMonoidˡ PEq.refl = PEq.refl
  IsPartialMonoidˡ.identityˡ binding-isMonoidˡ = ex []-sub sub-[] ∙-idˡ ∙-idʳ
  IsPartialMonoidˡ.identity⁻ˡ binding-isMonoidˡ (ex x₁ x₂ x₃ x₄) with sub-[]⁻ x₂ | []-sub⁻ x₁
  ... | PEq.refl , PEq.refl | PEq.refl , PEq.refl with ∙-id⁻ˡ x₃ | ∙-id⁻ʳ x₄
  ... | PEq.refl | PEq.refl = PEq.refl

  instance binding-isMonoid : IsPartialMonoid _≡_ binding-rel ([] ↕ [])
  binding-isMonoid = IsPartialMonoidˡ.partialMonoidˡ binding-isMonoidˡ

module _ where

  open import Data.Unit

  ups : ∀ {xs ys zs} → Binds (xs ↕ []) (ys ↕ []) zs → ∃ λ xys → zs ≡ (xys ↕ []) × xs ⊕ ys ≣ xys
  ups (ex x x₁ x₂ x₃) with []-sub⁻ x | []-sub⁻ x₁
  ... | PEq.refl , PEq.refl | PEq.refl , PEq.refl with ε∙ε x₃
  ... | PEq.refl = -, PEq.refl , x₂

  downs : ∀ {xs ys zs} → Binds ([] ↕ xs) ([] ↕ ys) zs → ∃ λ xys → zs ≡ ([] ↕ xys) × xs ⊗ ys ≣ xys
  downs (ex x x₁ x₂ x₃) with sub-[]⁻ x | sub-[]⁻ x₁
  ... | PEq.refl , PEq.refl | PEq.refl , PEq.refl with ε∙ε x₂
  ... | PEq.refl = -, PEq.refl , ∙-comm x₃

  module _ {P Q : Pred (List T) ℓ} where
    zipUp : ∀[ (Up P) ⊙ (Up Q) ⇒ Up (P ⊕ Q) ]
    zipUp ((↑ px) ∙⟨ σ ⟩ (↑ qx)) with ups σ
    ... | _ , PEq.refl , σ↑ = ↑ (px ∙⟨ σ↑ ⟩ qx) 

    zipDown : ∀[ (Down P) ⊙ (Down Q) ⇒ Down (P ⊗ Q) ]
    zipDown (↓ p ∙⟨ σ ⟩ ↓ q) with downs σ
    ... | _ , PEq.refl , σ↓ = ↓ (p ∙⟨ σ↓ ⟩ q)

  module _ {P Q : Pred (List T) ℓ} where

    upMap : ∀[ Up (P ─⊕ Q) ⇒ (Up P ─⊙ Up Q) ]
    upMap (↑ f) ⟨ σ ⟩ ↑ px with ups σ
    ... | _ , PEq.refl , σ↑ = ↑ (f ⟨ σ↑ ⟩ px)

    downMap : ∀[ Down (P ─⊗ Q) ⇒ (Down P ─⊙ Down Q) ]
    downMap (↓ f) ⟨ σ ⟩ ↓ px with downs σ
    ... | _ , PEq.refl , σ↓ = ↓ (f ⟨ σ↓ ⟩ px)

  binder : ∀ τ → ε[ Up (Just τ) ⊙ Down (Just τ) ]
  binder τ = (↑ PEq.refl ∙⟨ ex []-sub xs-xs≡ε ∙-idˡ ∙-idˡ ⟩ ↓ PEq.refl)
