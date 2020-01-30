{- An implementation of the VM monad -}
import MJ.Classtable.Core as Core

module JVM.Defaults.VM {c}(Ct : Core.Classtable c) where

open import JVM.Prelude hiding (_∥_)
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt; PT)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Permutation.Inductive hiding (swap)
open import Data.Product.Relation.Binary.Pointwise.NonDependent

open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.State
open import Relation.Ternary.Respect.Propositional
open import Relation.Ternary.Construct.Market
open import Relation.Ternary.Construct.Product

open import JVM.Defaults.Syntax Ct
open import JVM.Defaults.Syntax.Values Ct
open import JVM.Defaults.Semantics Ct using (View; VM)

open import Relation.Ternary.Data.Allstar


{- Callframes and the VM state -}
module _ where

  Frame : (ft : FrameTy) (Σ : World) → Set
  Frame ft = Allstar Ty Val locals-ty ✴ Allstar Ty Val stack-ty
    where open FrameTy ft

  variable
    ft₁ ft₂ ft₃ ft₄ ft : FrameTy

  VMState : FrameTy → Pred (World × World) 0ℓ
  VMState ft = Π₂ (Frame ft) ✴ λ where (Σ↑ , Σ↓) → Allstar Ty⁺ StoreVal Σ↑ Σ↓

M : LocalsTy → StackTy → StackTy → Pt View 0ℓ
M τ ψ₁ ψ₂ P v = State (VMState ⟨ τ , ψ₁ ⟩) {!⌜P!} {!!}

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
