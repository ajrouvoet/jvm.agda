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

    -- program manipulation
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
