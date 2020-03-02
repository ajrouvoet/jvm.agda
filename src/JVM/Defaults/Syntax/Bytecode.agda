-- Bytecode; i.e., instruction sequences; 
-- agnostic about the exact instructions, but opiniated about labels
open import Relation.Binary using (Rel)
open import Data.List hiding (concat)

module JVM.Defaults.Syntax.Bytecode {ℓ} (T : Set ℓ) where

open import Level
open import Relation.Unary hiding (_∈_; Empty)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Data.ReflexiveTransitive
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Data.Bigstar

open import Data.Sum
open import Data.Product

open import Relation.Ternary.Construct.Duplicate T
open import JVM.Model T

Labels = List T
private
  variable
    τ τ₁ τ₂ : T

open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional

Provides : T → Pred Binding ℓ
Provides τ (u ↕ d) = τ ∈ u

-- Decide whether an element is left or right of a disjoint split
lorr : ∀ {u₁ u₂ t u} → u₁ ⊕ u₂ ≣ u → t ∈ u → t ∈ u₁ ⊎ t ∈ u₂
lorr (consˡ σ) (here refl) = inj₁ (here refl)
lorr (consʳ σ) (here refl) = inj₂ (here refl)
lorr (consˡ σ) (there e) with lorr σ e
... | inj₁ e' = inj₁ (there e')
... | inj₂ e' = inj₂ e'
lorr (consʳ σ) (there e) with lorr σ e
... | inj₁ e' = inj₁ e'
... | inj₂ e' = inj₂ (there e')

lemma : ∀ {xs ys zs} {z} → xs - ys ≣ zs → z ∈ exp zs → z ∈ ys
lemma (sub x x₁ x₂) e = wk x₁ e
  where
    wk : ∀ {xs ys zs} {z} → xs ⊗ ys ≣ zs → z ∈ xs → z ∈ zs
    wk (overlaps σ) (here refl) = here refl
    wk (consˡ σ) (here refl)      = here refl
    wk (consʳ σ) (here refl)      = there (wk σ (here refl))

    wk (overlaps σ) (there e)   = there (wk σ e)
    wk (consˡ σ) (there e)        = there (wk σ e)
    wk (consʳ σ) (there e)        = there (wk σ (there e))

-- Things provided must be on the left or right of a split
crumb : ∀ {c} {as bs cs : Binding} → Provides c cs → as ∙ bs ≣ cs → (Provides c as) ⊎ (Provides c bs)
crumb e (ex x₁ x₂ x₃ x₄) with lorr x₃ e
... | inj₁ l = inj₁ (lemma x₂ l)
... | inj₂ r = inj₂ (lemma x₁ r)

{- The internals of a zipper: we account binding with the "Global binding" (/Exchange) PRSA -}
Labeled : T → Pred Binding ℓ
Labeled τ = Emp ∪ Up (Just τ)

Labeling : T → Pred (List T) _
Labeling = λ τ → Bigstar {{r = disjoint-split}} (Just τ) 

module Codes (I : T → T → List T → Set ℓ) where

  open import Data.Unit.Polymorphic

  data Code : T → T → Pred Binding ℓ where
    labeled : ∀[ Up (Labeling τ₁) ⊙ Down (I τ₁ τ₂) ⇒ Code τ₁ τ₂ ]
    instr   : ∀[ Down (I τ₁ τ₂) ⇒ Code τ₁ τ₂ ]

  label : ∀[ Up (Labeling τ₁) ⇒ Code τ₁ τ₂ ─⊙ Code τ₁ τ₂ ]
  label l ⟨ σ ⟩ instr i   = labeled (l ∙⟨ σ ⟩ i)
  label l ⟨ σ ⟩ labeled (l₂∙i) with ⊙-assocₗ (l ∙⟨ σ ⟩ l₂∙i)
  ... | l₁∙l₂ ∙⟨ σ′ ⟩ i with upMap (↑ (⊙-curry (arrow concat))) ⟨ ∙-idˡ ⟩ zipUp l₁∙l₂
  ... | ls = labeled (ls ∙⟨ σ′ ⟩ i)

  ⟪_⇒_⟫ : T → T → Pred Binding ℓ
  ⟪ τ₁ ⇒ τ₂ ⟫ = Star Code τ₁ τ₂

  ⟪_⇒_⟫+ : T → T → Pred Binding ℓ
  ⟪ τ₁ ⇒ τ₂ ⟫+ = Plus Code τ₁ τ₂

  ⟪_⇐_⟫ : T → T → Pred Binding ℓ
  ⟪ τ₂ ⇐ τ₁ ⟫ = Star (flip Code) τ₁ τ₂
    where open import Function using (flip)

  {- The zipper structure for walking over bytecode with focus -}
  module _ where
    private
      Zipper′ = λ a b c d → ⟪ a ⇐ b ⟫ ⊙ (Code b c) ⊙ ⟪ c ⇒ d ⟫

    data Zipper : (b c d : T) → Pred Labels ℓ where
      zipped : ∀ {a b c d} → ∀[ (λ Φ → Zipper′ a b c d (Φ ↕ [])) ⇒ Zipper b c d ]
      ended  : ∀ {a b}     → ∀[ (λ Φ → ⟪ a ⇐ b ⟫ (Φ ↕ [])) ⇒ Zipper b b b ]

    -- rewind with an accumulator to a labeled instruction
    -- {-# TERMINATING #-}
    -- left : ∀ {a b c e} → ∀[ (⟪ a ⇐ b ⟫ ∩ Provides e) ⇒ ⟪ b ⇒ c ⟫ ─⊙ (⋃[ f ∶ _ ] Zipper′ a e f c) ]
    -- left (i ▹⟨ σ₁ ⟩ is , snd) ⟨ σ₂ ⟩ acc with crumb snd σ₁
    -- ... | inj₂ r with ∙-assocᵣ (∙-comm σ₁) σ₂
    -- ... | _ , σ₃ , σ₄ = left (is , r) ⟨ σ₃ ⟩ (i ▹⟨ σ₄ ⟩ acc)

    -- -- points to a label;
    -- -- we found the instruction we were looking for,
    -- -- now we just forward again to the first code point that is not a label
    -- left (labeled i ▹⟨ σ₁ ⟩ is , snd) ⟨ σ₂ ⟩ acc | inj₁ (here refl) with ∙-assocᵣ (∙-comm σ₁) σ₂
    -- ... | _ , σ₃ , σ₄ = {!!} -- -, is ∙⟨ σ₃ ⟩ (labeled i ∙⟨ σ₄ ⟩ acc)

    -- {- wind fwd with an accumulator to a labeled instruction -}
    -- {-# TERMINATING #-}
    -- right : ∀ {a b c e} → ∀[ (⟪ b ⇒ c ⟫ ∩ Provides e) ⇒ ⟪ a ⇐ b ⟫ ─⊙ (⋃[ f ∶ _ ] Zipper′ a e f c) ]
    -- right (i ▹⟨ σ₁ ⟩ is , snd) ⟨ σ₂ ⟩ acc with crumb snd σ₁
    -- ... | inj₂ r with ∙-assocᵣ (∙-comm σ₁) σ₂
    -- ... | _ , σ₃ , σ₄ = right (is , r) ⟨ σ₃ ⟩ i ▹⟨ σ₄ ⟩ acc

    -- right (labeled i ▹⟨ σ₁ ⟩ is , snd) ⟨ σ₂ ⟩ acc  | inj₁ (here refl) =
    --   -, acc ∙⟨ ∙-comm σ₂ ⟩ (labeled i) Rel₃.∙⟨ σ₁ ⟩ is 

    -- {- Walk through a zipper using a label -}
    -- jump : ∀ {a b c d e : T} → ∀[ (Zipper′ a b c d ∩ Provides e) ⇒ ⋃[ f ∶ _ ] Zipper′ a e f d ]
    -- jump (is ∙⟨ σ ⟩ js , p) with crumb p σ
    -- ... | inj₁ l = left (is , l) ⟨ σ ⟩ cons js
    -- ... | inj₂ r = right (cons js , r) ⟨ ∙-comm σ ⟩ is

    -- moveᵣ : ∀[ Zipper τ₁ τ₂ τ ⇒ ⋃[ τ₃ ∶ _ ] Zipper τ₂ τ₃ τ ]
    -- moveᵣ (ended z) = -, ended z
    -- moveᵣ (zipped z) with ⊙-assocₗ z
    -- moveᵣ (zipped z) | bwd ∙⟨ σ ⟩ nil rewrite ∙-id⁻ʳ σ = -, ended (cons (⊙-swap bwd))
    -- moveᵣ (zipped z) | bwd ∙⟨ σ ⟩ i ▹⟨ σ₂ ⟩ is = -, zipped (cons (⊙-swap bwd) ∙⟨ σ ⟩ i ∙⟨ σ₂ ⟩ is)

    -- postulate focus : ∀[ Zipper τ₁ τ₂ τ ⇒ (Zipper τ₁ τ₂ τ ⊙ (Empty (τ₁ ≡ τ₂ × τ₂ ≡ τ) ∪ (I τ₁ τ₂))) ]
    -- -- focus z@(zipped (bwd ∙⟨ σ₁ ⟩ ↑ f ∙⟨ σ₂ ⟩ fwd)) =
    -- --   let y = ⊙-assocᵣ (copy f ∙⟨ σ₂ ⟩ fwd) in ?
    -- -- focus z@(ended x)  = z ∙⟨ ∙-idʳ ⟩ inj₁ refl
