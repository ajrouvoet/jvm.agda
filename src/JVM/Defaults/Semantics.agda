import MJ.Classtable.Core as Core

module JVM.Defaults.Semantics {c}(Ct : Core.Classtable c) where

open import JVM.Prelude hiding (_∥_)
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt; PT)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Permutation.Inductive hiding (swap)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Ternary.Monad
open import Relation.Ternary.Respect.Propositional

open import JVM.Defaults.Syntax Ct
open import JVM.Defaults.Syntax.Values Ct

module _ where
  
  open import Relation.Binary.Structures
  open import Relation.Ternary.Construct.Product
  open import Relation.Ternary.Construct.Market renaming (_≈_ to Market[_≈_]; ≈-equiv to market-equiv)

  open import JVM.Defaults.Syntax.Labels Ct using (Labels)

  -- client view
  View = Labels × World

  instance view-rel : Rel₃ View
  view-rel = ctx-rel ×-∙ ctx-rel

  instance view-semigroup : IsPartialSemigroup _≡_ view-rel
  view-semigroup = Propositional.×-isPartialSemigroup

  instance view-partialmonoid : IsPartialMonoid _≡_ view-rel ([] , [])
  view-partialmonoid = Propositional.×-isPartialMonoid-≡

  instance view-commutative : IsCommutative view-rel
  view-commutative = {!!}

  -- exported type-formers
  open import Relation.Ternary.Construct.Product using (Π₂; Π₁; fst; snd) public

record VM (M : LocalsTy → StackTy → StackTy → Pt View 0ℓ) : Set₁ where
  field
    {{ monad }} : ∀ {τ} → Monad StackTy (λ where ψ₁ ψ₂ → M τ ψ₁ ψ₂)

    vmget    : a ∈ τ → ε[ M τ ψ ψ (Π₂ (Val a)) ]
    vmset    : a ∈ τ → ∀[ Π₂ (Val a) ⇒ M τ ψ ψ Emp ]
    vmpush   : ∀[ Π₂ (Val a)         ⇒ M τ ψ (a ∷ ψ) Emp ]
    vmpop    : ε[ M τ (a ∷ ψ) ψ (Π₂ (Val a)) ]
    vmjmp    : ∀[ Π₁ (Just ψ) ⇒ M τ ψ ψ Emp ]

    drop     : ∀ {P : Pred View 0ℓ} → ∀[ P ⇒ M τ ψ ψ Emp ]

open VM {{...}}

eval : ∀ {M} {{_ :  VM M}} → ∀[ Π₁ ⟨ τ ∣ ψ₁ ⇒ ψ₂ ⟩ ⇒ M τ ψ₁ ψ₂ Emp ]

eval (fst noop)      = do
  return refl

eval (fst pop)       = do
  v ← vmpop 
  drop {P = Π₂ (Val _)} v

eval (fst (push c))  = do
  vmpush (snd (constvalue c))

eval (fst dup)       = do
  v             ← vmpop
  v ×⟨ σ ⟩ refl ← vmpush v &⟨ Π₂ (Val _) # dupn , dupn ⟩ v
  vmpush (coe (∙-id⁻ʳ σ) v)

eval (fst swap)      = do
  w              ← vmpop
  w ×⟨ σ₁ ⟩ v    ← vmpop    &⟨ Π₂ (Val _) # ∙-idʳ     ⟩ w
  v ×⟨ σ₂ ⟩ refl ← vmpush w &⟨ Π₂ (Val _) # ∙-comm σ₁ ⟩ v
  vmpush (coe (∙-id⁻ʳ σ₂) v)

eval (fst (load x))  = do
  v ← vmget x
  vmpush v

eval (fst (store x)) = do
  v ← vmpop
  vmset x v

eval (fst (goto lbl)) = do
  vmjmp (fst lbl)

eval (fst (if lbl)) = do
  lbl ×⟨ σ ⟩ snd (num zero) ← vmpop &⟨ Π₁ (Just _) # ∙-idʳ ⟩ fst lbl
    where
      lbl ×⟨ _ ⟩ snd (num (suc n)) → drop lbl
  vmjmp (coe (∙-id⁻ʳ σ) lbl)

{- An implementation of the VM monad -}
module _ where

--   -- server view
--   Server     = Intf × Market World

--   instance car-rel : Rel₃ Server
--   car-rel = exchange-rel ×-∙ market-rel

--   Server[_≈_] : Server → Server → Set _
--   Server[_≈_] = Pointwise Intf[_≈_] Market[_≈_]

--   instance car-≈-equiv : IsEquivalence Server[_≈_]
--   car-≈-equiv = ×-isEquivalence account-equiv market-equiv

--   instance car-semigroup : IsPartialSemigroup Server[_≈_] car-rel
--   car-semigroup = ×-isSemigroup

--   instance car-partialmonoid : IsPartialMonoid Server[_≈_] car-rel (ε , ε)
--   car-partialmonoid = ×-isPartialMonoid

--   data Client {ℓ} : PT View Server ℓ ℓ where
--     client : ∀ {P w} → P (ι , w) → Client P ([] ↕ ι , demand w)

  -- M : (ι₁ ι₂ : Labels) → LocalsTy → (ψ₁ ψ₂ : StackTy) → Pt World 0ℓ
  -- M ι₁ ι₂ τ ψ₁ ψ₂ P μ = ∀[ Frame ⟨ τ ∣ ψ₁ ⟩ ✴ Zipper τ ψ₁ ι ⇒ Frame ⟨ τ ∣ ψ₂ ⟩ ✴ Zipper τ ψ₂ ι ✴ P ]
