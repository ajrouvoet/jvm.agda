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

open import Relation.Ternary.Construct.List.Overlapping T as O public
open import Data.Unit

open import Relation.Ternary.Construct.Empty T
open import Relation.Ternary.Construct.List.Disjoint T as D public hiding (threeway; _∈_)

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

  {- cross-split between two notions of separation -}
  xsplit : ∀ {a b c d z} →
        a ⊗ b ≣ z → c ⊕ d ≣ z →
        Σ[ frags ∈ (Labels × Labels × Labels × Labels) ] 
        let ac , ad , bc , bd = frags
        in ac ⊕ ad ≣ a × bc ⊕ bd ≣ b × ac ⊗ bc ≣ c × ad ⊗ bd ≣ d

  xsplit [] [] = -, ∙-idˡ , ∙-idˡ , ∙-idˡ , ∙-idˡ

  xsplit (overlaps σ₁) (consˡ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, D.consˡ σ₃ , D.consˡ σ₄ , overlaps σ₅ , σ₆

  xsplit (overlaps σ₁) (consʳ σ₂)  with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, D.consʳ σ₃ , D.consʳ σ₄ , σ₅ , overlaps σ₆

  xsplit (consˡ σ₁) (consˡ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, D.consˡ σ₃ , σ₄ , O.consˡ σ₅ , σ₆

  xsplit (consˡ σ₁) (consʳ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, D.consʳ σ₃ , σ₄ , σ₅ , O.consˡ σ₆

  xsplit (consʳ σ₁) (consˡ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, σ₃ , D.consˡ σ₄ , O.consʳ σ₅ , σ₆
  xsplit (consʳ σ₁) (consʳ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, σ₃ , D.consʳ σ₄ , σ₅ , O.consʳ σ₆

  {- One side of the reverse -}
  xup : ∀ {a b ab c bc} → a ⊕ b ≣ ab → b ⊗ c ≣ bc → ∃ λ abc → a ⊕ bc ≣ abc × ab ⊗ c ≣ abc
  xup σ₁ []            = -, σ₁ , ∙-idʳ
  xup σ₁ (consʳ σ₂) with xup σ₁ σ₂
  ... | _ , σ₃ , σ₄ = -, D.consʳ σ₃ , O.consʳ σ₄
  xup (consˡ σ₁) σ₂@(overlaps _) with xup σ₁ σ₂
  ... | _ , σ₃ , σ₄ = -, D.consˡ σ₃ , O.consˡ σ₄
  xup (consˡ σ₁) σ₂@(consˡ _) with xup σ₁ σ₂
  ... | _ , σ₃ , σ₄ = -, D.consˡ σ₃ , O.consˡ σ₄
  xup (consʳ σ₁) (overlaps σ₂) with xup σ₁ σ₂
  ... | _ , σ₃ , σ₄ = -, D.consʳ σ₃ , overlaps σ₄
  xup (consʳ σ₁) (consˡ σ₂) with xup σ₁ σ₂
  ... | _ , σ₃ , σ₄ = -, D.consʳ σ₃ , O.consˡ σ₄ 

  xup² : ∀ {a b a' b' e₁ e₂ ab} →
         e₁ ⊗ a' ≣ a → e₂ ⊗ b' ≣ b → a' ⊕ b' ≣ ab →
         ∃₂ λ ab' e₁₂ → a ⊕ b ≣ ab' × ab ⊗ e₁₂ ≣ ab' × e₁ ⊗ e₂ ≣ e₁₂
  xup² σ₁ σ₂ σ₃ with xup σ₃ (∙-comm σ₂)
  ... | _ , σ₄ , σ₅ with xup (∙-comm σ₄) (∙-comm σ₁)
  ... | _ , σ₆ , σ₇ with ∙-assocᵣ σ₅ σ₇
  ... | _ , σ₈ , σ₉ = -, -, ∙-comm σ₆ , σ₈ , ∙-comm σ₉

  {- Another side of the reverse -}
  xdown : ∀ {a b ab c bc} → a ⊗ b ≣ ab → b ⊕ c ≣ bc → ∃ λ abc → a ⊗ bc ≣ abc × ab ⊕ c ≣ abc
  xdown σ₁ [] = -, σ₁ , ∙-idʳ
  xdown σ₁ (consʳ σ₂) with xdown σ₁ σ₂
  ... | _ , σ₃ , σ₄  = -, O.consʳ σ₃ , D.consʳ σ₄
  xdown (overlaps σ₁) (consˡ σ₂) with xdown σ₁ σ₂
  ... | _ , σ₃ , σ₄ = -, overlaps σ₃ , D.consˡ σ₄
  xdown (consˡ σ₁) σ₂@(consˡ _) with xdown σ₁ σ₂
  ... | _ , σ₃ , σ₄ = -, O.consˡ σ₃ , D.consˡ σ₄
  xdown (consʳ σ₁) (consˡ σ₂) with xdown σ₁ σ₂
  ... | _ , σ₃ , σ₄ = -, O.consʳ σ₃ , D.consˡ σ₄

  xdown² : ∀ {a b a' b' e₁ e₂ ab} →
           e₁ ⊕ a' ≣ a → e₂ ⊕ b' ≣ b → a' ⊗ b' ≣ ab →
           ∃₂ λ ab' e₁₂ → a ⊗ b ≣ ab' × ab ⊕ e₁₂ ≣ ab' × e₁ ⊕ e₂ ≣ e₁₂
  xdown² σ₁ σ₂ σ₃ with xdown σ₃ (∙-comm σ₂) 
  ... | _ , σ₄ , σ₅ with xdown (∙-comm σ₄) (∙-comm σ₁)
  ... | _ , σ₆ , σ₇ with ∙-assocᵣ σ₅ σ₇
  ... | _ , σ₈ , σ₉ = -, -, ∙-comm σ₆ , σ₈ , ∙-comm σ₉

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

  binding-semigroupˡ : IsPartialSemigroupˡ _≡_ binding-rel
  IsPartialSemigroupˡ.≈-equivalence binding-semigroupˡ = PEq.isEquivalence
  IsPartialSemigroupˡ.assocᵣ binding-semigroupˡ
    {a = a↑ ↕ a↓} {b = b↑ ↕ b↓} {ab = ab↑ ↕ ab↓} {c = c↑ ↕ c↓} {abc = abc↑ ↕ abc↓}
    (ex (sub {e = eb>a} {e' = eb>a'} {d' = a↓'} {u' = b↑'} τ-a↓ τ-b↑ ρ₁)
        (sub {e = ea>b} {e' = ea>b'} {d' = b↓'} {u' = a↑'} τ-b↓ τ-a↑ ρ₂) σ-ab↑ σ-ab↓)
    (ex (sub {e = ec>ab} {e' = ec>ab'} {d' = ab↓'} {u' = c↑'} τ-ab↓ τ-c↑ ρ₃)
        (sub {e = eab>c} {e' = eab>c'} {d' = c↓'} {u' = ab↑'} τ-c↓ τ-ab↑ ρ₄) σ-abc↑ σ-abc↓)
      with xsplit τ-ab↑ σ-ab↑ | xsplit σ-ab↓ τ-ab↓
  ... | (a↑'' , b↑'' , ea>c , eb>c) , ν₁ , ν₂ , ν₃ , ν₄ | (b↓'' , ec>b , a↓'' , ec>a) , μ₁ , μ₂ , μ₃ , μ₄ with ∙-assocᵣ ν₁ σ-abc↑ | ∙-assocᵣ μ₃ (∙-comm σ-abc↓)
  ... | bc↑ , ι₁ , ι₂ | bc↓ , κ₁ , κ₂ with ∙-rotateᵣ (∙-comm τ-b↑) ν₄ | ∙-rotateᵣ (∙-comm τ-b↓) μ₁
  ... | b↑''' , α-b↑ , ν₅ | b↓''' , α-b↓ , μ₅ with xup² ν₅ (∙-comm τ-c↑) ι₂ | xdown² (∙-comm μ₂) (∙-comm τ-c↓) κ₂
  ... | bc↑' , ebc>a , σ-bc↑ , τ-bc↑ , ζ-ebc>a | bc↓' , ea>bc , σ-bc↓ , τ-bc↓ , ζ-ea>bc = {!!}

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
