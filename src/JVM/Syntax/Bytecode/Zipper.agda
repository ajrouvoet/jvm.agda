{- The zipper structure for walking over bytecode with focus -}

{-# OPTIONS --no-qualified-instances #-}
open import Data.List hiding (concat)

module JVM.Defaults.Syntax.Bytecode.Zipper {ℓ}
  (T : Set ℓ) (⟨_⇒_⟩ : T → T → List T → Set ℓ) (nop : ∀ {τ} → ⟨ τ ⇒ τ ⟩ []) where

open import Level
open import Function using (case_of_)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Data.ReflexiveTransitive

open import JVM.Model T
open import JVM.Defaults.Syntax.Bytecode T ⟨_⇒_⟩ nop

private
  variable
    τ₁ τ₂ τ₃ τ₄ : T

  Context = λ a b c d → ⟪ a ⇐ b ⟫ ⊙ ⟪ c ⇒ d ⟫

  Focused : (a b c d : T) → Pred Intf ℓ
  Focused a b c d = (Code b c) ⊙ Context a b c d

data Zipper : (b c d : T) → Pred Intf ℓ where
  ended   : ∀ {a b}     → ∀[ ⟪ a ⇐ b ⟫       ⇒ Zipper b b b ]
  focused : ∀ {a b c d} → ∀[ Focused a b c d ⇒ Zipper b c d ]

open import Relation.Ternary.Construct.Market Overlap.bags as Market
open import Relation.Ternary.Monad.State Overlap.bags

open Market.WithCommutativeMonoid Overlap.bags-isMonoid Overlap.bags-isCommutative

ZipperT : (M : Pt Market ℓ) → T → T → T → Pt (List T) ℓ
ZipperT M a b c = StateT M (Up⁻ (Zipper a b c))

module _
  {M : Pt Market ℓ}
  {{mm : Monad ⊤ (λ _ _ → M)}}
  {{mr : ∀ {P} → Respect _≈_ (M P) }} where

  module _ {a b c : T} where
    open StateTransformer M {{mm}} {Up⁻ (Zipper a b c)} public

  -- This law explains the relation between the inside invariant of a closed zipper,
  -- and the outside invariant of the state monad.
  escape : ∀ {P Q} → {{_ : Respect _≈intf≈_ Q}} → ∀[ ● (Up⁻ (Down P ⊙ Q)) ⇒ ○ P ⊙ ● (Up⁻ Q) ]
  escape (lift (↓ px ∙⟨ σ ⟩ qx)) =
    let _ , eq , σ' = up-down=up σ in (lift px) ∙⟨ offerᵣ (∙-comm σ') ⟩ (lift (coe eq qx))

  getFocus : ε[ ZipperT M τ₁ τ₂ τ₃ ⟨ τ₁ ⇒ τ₂ ⟩ ]
  getFocus ⟨ σ ⟩ lift (ended x)   = do return (lift nop ∙⟨ σ ⟩ (lift (ended x)))
  getFocus ⟨ σ ⟩ lift (focused z) = do
    let ○f ∙⟨ σ' ⟩ ●z = escape (lift (focus z))
    coe (∙-id⁻ˡ σ) (return (○f ∙⟨ σ' ⟩ ●-map focused ●z))
    where
      focus : ∀[ Focused τ₁ τ₂ τ₃ τ₄ ⇒ Down ⟨ τ₂ ⇒ τ₃ ⟩ ⊙ Focused τ₁ τ₂ τ₃ τ₄ ]
      focus (c ∙⟨ σ ⟩ ctx) = ⊙-assocᵣ (getInstr c ∙⟨ σ ⟩ ctx)

-- newZipper : ∀ {τ₁ τ₂} → ∀[ Up⁻ ⟪ τ₁ ⇒ τ₂ ⟫ ⇒ ⋃[ τ₃ ∶ _ ] Zipper τ₁ τ₃ τ₂ ]
-- newZipper nil           = -, ended nil
-- newZipper (i ▹⟨ σ ⟩ is) = -, focused (i ∙⟨ σ ⟩ nil ∙⟨ ∙-idˡ ⟩ is)

-- mover : ∀[ Zipper τ₁ τ₂ τ₃ ⇒ ⋃[ τ₄ ∶ _ ] Zipper τ₂ τ₄ τ₃ ]
-- mover (ended x)       = -, ended x
-- mover (focused f∙ctx) =
--   let nxt ∙⟨ σ₁ ⟩ f∙pvs = ⊙-rotateᵣ f∙ctx in case nxt of λ where
--     nil            → -, ended (coe (∙-id⁻ˡ σ₁) (cons f∙pvs))
--     (i ▹⟨ σ₂ ⟩ is) → -, focused (⊙-rotateₗ (⊙-assocᵣ ((is ∙⟨ ∙-comm σ₂ ⟩ i) ∙⟨ σ₁ ⟩ cons f∙pvs)))

-- next : ∀[ Zipper τ₁ τ₂ τ₃ ⇒ I τ₁ τ₂ ⊙ ⋃[ τ₄ ∶ _ ] Zipper τ₂ τ₄ τ₃ ]
-- next z = let f ∙⟨ σ ⟩ z' = getFocus z in f ∙⟨ σ ⟩ mover z'

-- data Cont : Pred (List T) ℓ where
--   ok   : ε[ Cont ]
-- --   jmp  : ∀[ Π₁ (Just ψ) ⇒ Res ]
-- --   nope : ε[ Res ]

-- open import Data.Product.Relation.Binary.Pointwise.NonDependent

-- module _
--   {R : Set ℓ} {uᵣ}
--   {M : T → T → Pt (List T × R) ℓ}
--   {{rel : Rel₃ R}} {e} {_≈ᵣ_  : R → R → Set e} {{_ : IsPartialMonoid _≈ᵣ_ rel uᵣ}}
--   {{_ : Monad T M}} {{_ : ∀ {τ₁ τ₂} {P : Pred (List T × R) ℓ} → Respect (Pointwise Disjoint._≈_ _≈ᵣ_) (M τ₁ τ₂ P) }}
--   where
   
--   Res : Pred (List T × R) ℓ
--   Res = True {ℓ = ℓ} ∪ True {ℓ = ℓ}

--   {-# NON_TERMINATING #-}
--   interpret : (∀ {τ₁ τ₂} → ∀[ Π₁ (I τ₁ τ₂) ⇒ M τ₁ τ₂ (Π₁ Cont) ]) → ∀[ Π₁ (Up⁻ ⟪ τ₁ ⇒ τ₂ ⟫) ⇒ M τ₁ τ₂ Res ]
--   interpret step (fst is) = run (fst (proj₂ (newZipper is)))
--     where
--       run : ∀[ Π₁ (Zipper τ₁ τ₂ τ₃) ⇒ M τ₁ τ₃ Res ]
--       run (fst (ended _))     = return (inj₂ _)
--       run (fst z@(focused _)) = do
--         let i ∙⟨ σ ⟩ z = next z
--         z ∙⟨ σ ⟩ fst ok ← step (fst i) &⟨ Π₁ _ # ∙-comm σ , ∙-idˡ ⟩ fst (proj₂ z)
--         coe (∙-id⁻ʳ σ) (run z)

-- Decide whether an element is left or right of a disjoint split
-- postulate lorr : ∀ {u₁ u₂ t u} → u₁ ⊕ u₂ ≣ u → t ∈ u → t ∈ u₁ ⊎ t ∈ u₂
-- lorr (consˡ σ) (here refl) = inj₁ (here refl)
-- lorr (consʳ σ) (here refl) = inj₂ (here refl)
-- lorr (consˡ σ) (there e) with lorr σ e
-- ... | inj₁ e' = inj₁ (there e')
-- ... | inj₂ e' = inj₂ e'
-- lorr (consʳ σ) (there e) with lorr σ e
-- ... | inj₁ e' = inj₁ e'
-- ... | inj₂ e' = inj₂ (there e')

-- postulate lemma : ∀ {xs ys zs} {z} → xs - ys ≣ zs → z ∈ up zs → z ∈ ys
-- lemma (sub x x₁ x₂) e = wk x₁ e
--   where
--     wk : ∀ {xs ys zs} {z} → xs ⊗ ys ≣ zs → z ∈ xs → z ∈ zs
--     wk (overlaps σ) (here refl) = here refl
--     wk (consˡ σ) (here refl)      = here refl
--     wk (consʳ σ) (here refl)      = there (wk σ (here refl))

--     wk (overlaps σ) (there e)   = there (wk σ e)
--     wk (consˡ σ) (there e)        = there (wk σ e)
--     wk (consʳ σ) (there e)        = there (wk σ (there e))

-- Provides : T → Pred Intf ℓ
-- Provides τ (u ⇅ d) = τ ∈ u

-- Things provided must be on the left or right of a split
-- crumb : ∀ {c} {as bs cs : Intf} → Provides c cs → as ∙ bs ≣ cs → (Provides c as) ⊎ (Provides c bs)
-- crumb e (ex x₁ x₂ x₃ x₄) with lorr x₃ e
-- ... | inj₁ l = inj₁ (lemma x₂ l)
-- ... | inj₂ r = inj₂ (lemma x₁ r)

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
-- moveᵣ (focused z) with ⊙-assocₗ z
-- moveᵣ (focused z) | bwd ∙⟨ σ ⟩ nil rewrite ∙-id⁻ʳ σ = -, ended (cons (⊙-swap bwd))
-- moveᵣ (focused z) | bwd ∙⟨ σ ⟩ i ▹⟨ σ₂ ⟩ is = -, focused (cons (⊙-swap bwd) ∙⟨ σ ⟩ i ∙⟨ σ₂ ⟩ is)

-- postulate focus : ∀[ Zipper τ₁ τ₂ τ ⇒ (Zipper τ₁ τ₂ τ ⊙ (Empty (τ₁ ≡ τ₂ × τ₂ ≡ τ) ∪ (I τ₁ τ₂))) ]
-- -- focus z@(focused (bwd ∙⟨ σ₁ ⟩ ⇅ f ∙⟨ σ₂ ⟩ fwd)) =
-- --   let y = ⊙-assocᵣ (copy f ∙⟨ σ₂ ⟩ fwd) in ?
-- -- focus z@(ended x)  = z ∙⟨ ∙-idʳ ⟩ inj₁ refl
