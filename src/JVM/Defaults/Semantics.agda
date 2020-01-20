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
open import Data.Empty

open import JVM.Defaults.Syntax Ct
open import JVM.Defaults.Syntax.Values Ct

-- We define the 'view' of a client on the server (VM) state typing.
-- This is analogue to the State monad (i.e., the server) internally operating on (Market A), where clients only see (A).
-- The view consists of a set of labels that the clients uses, as well as a number of heap cells that it sees.
--
-- We manually repeat the relevant instances for this view here to speed up instance search.
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
  view-commutative = ×-isCommutative

  -- exported type-formers
  open import Relation.Ternary.Construct.Product using (Π₂; Π₁; fst; snd) public

-- Typing jump computations:
-- Things that do not work
--   - Indexing with 'current instruction typing':
--     next/jump instruction type is partially existentially quantified.
--   - Jump as an exception: this makes the post-stack typing index unreliable.

-- The API of a virtual machine
record VM (M : LocalsTy → StackTy → StackTy → Pt View 0ℓ) : Set₁ where
  field
    {{ monad }} : ∀ {τ} → Monad StackTy (λ where ψ₁ ψ₂ → M τ ψ₁ ψ₂)

    -- register manipulation
    vmget    : a ∈ τ → ε[ M τ ψ ψ (Π₂ (Val a)) ]
    vmset    : a ∈ τ → ∀[ Π₂ (Val a) ⇒ M τ ψ ψ Emp ]

    -- stack manipulation
    vmpush   : ∀[ Π₂ (Val a)         ⇒ M τ ψ (a ∷ ψ) Emp ]
    vmpop    : ε[ M τ (a ∷ ψ) ψ (Π₂ (Val a)) ]

    drop     : ∀ {P : Pred View 0ℓ} → ∀[ P ⇒ M τ ψ ψ Emp ]

open VM {{...}}

data Res : Pred View 0ℓ where
  ok  : ε[ Res ]
  jmp : ∀[ Π₁ (Just ψ) ⇒ Res ]

eval : ∀ {M} {{_ :  VM M}} → ∀[ Π₁ ⟨ τ ∣ ψ₁ ⇒ ψ₂ ⟩ ⇒ M τ ψ₁ ψ₂ Res ]

eval (fst noop) = do
  return ok

eval (fst pop) = do
  v ← vmpop 
  refl ← drop {P = Π₂ (Val _)} v
  return ok

eval (fst (push c)) = do
  refl ← vmpush (snd (constvalue c))
  return ok

eval (fst dup) = do
  v             ← vmpop
  v ×⟨ σ ⟩ refl ← vmpush v &⟨ Π₂ (Val _) # dupn , dupn ⟩ v
  refl ← vmpush (coe (∙-id⁻ʳ σ) v)
  return ok

eval (fst swap) = do
  w              ← vmpop
  w ×⟨ σ₁ ⟩ v    ← vmpop    &⟨ Π₂ (Val _) # ∙-idʳ     ⟩ w
  v ×⟨ σ₂ ⟩ refl ← vmpush w &⟨ Π₂ (Val _) # ∙-comm σ₁ ⟩ v
  refl ← vmpush (coe (∙-id⁻ʳ σ₂) v)
  return ok

eval (fst (load x))  = do
  v ← vmget x
  refl ← vmpush v
  return ok

eval (fst (store x)) = do
  v ← vmpop
  refl ← vmset x v
  return ok

eval (fst (goto lbl)) = do
  return (jmp (fst lbl))

eval (fst (if lbl)) = do
  lbl ×⟨ σ ⟩ snd (num zero) ← vmpop &⟨ Π₁ (Just _) # ∙-idʳ ⟩ fst lbl
    where
      lbl ×⟨ _ ⟩ snd (num (suc n)) → do
        refl ← drop lbl
        return ok
  return (jmp (coe (∙-id⁻ʳ σ) lbl))
