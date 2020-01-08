import MJ.Classtable.Core as Core

module JVM.Defaults.Semantics {c}(Ct : Core.Classtable c) where

open import Prelude hiding (_∥_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Relation.Ternary.Monad
open import Relation.Ternary.Respect.Propositional

open import JVM.Defaults.Syntax Ct
open import JVM.Defaults.Syntax.Values Ct

record VM (M : Labels → LocalsTy → StackTy → StackTy → Pt World 0ℓ) : Set₁ where
  field
    {{ monad }} : Monad StackTy (M ι τ)
    vmget    : a ∈ τ → ∀[         M ι τ ψ ψ (Val a) ]
    vmset    : a ∈ τ → ∀[ Val a ⇒ M ι τ ψ ψ Emp ]
    vmpush   : ∀[ Val a         ⇒ M ι τ ψ (a ∷ ψ) Emp ]
    vmpop    : ε[                 M ι τ (a ∷ ψ) ψ (Val a) ]
    vmjmp    : ψ ∈ ι → ε[         M ι τ ψ ψ Emp ]

open VM {{...}}

eval : ∀ {M} {{_ :  VM M}} → ⟨ τ ∣ ψ₁ ⇒ ψ₂ ⟩ ι → ε[ M ι τ ψ₁ ψ₂ U ]
eval noop = do
  return tt
eval pop = do
  v              ← vmpop
  return tt
eval (push c) = do
  refl           ← vmpush (constvalue c)
  return tt
eval dup = do
  v              ← vmpop
  refl ×⟨ σ ⟩ v  ← vmpush v &⟨ Val _ ∥ dupn ⟩ v
  refl           ← vmpush (coe (∙-id⁻ˡ σ) v)
  return tt
eval swap = do
  w              ← vmpop
  v ×⟨ σ₁ ⟩ w    ← vmpop &⟨ Val _ ∥ ∙-idˡ ⟩ w
  refl ×⟨ σ₂ ⟩ v ← vmpush w &⟨ Val _ ∥ ∙-comm σ₁ ⟩ v
  refl           ← vmpush (coe (∙-id⁻ˡ σ₂) v)
  return tt
eval (load x) = do
  v              ← vmget x
  refl           ← vmpush v
  return tt
eval (store x) = do
  v              ← vmpop
  refl           ← vmset x v
  return tt
eval (goto refl) = do
  refl ← vmjmp (here refl)
  return tt
eval (if refl)   = do
  num zero       ← vmpop
    where
      num (suc n) → return tt
  refl ← vmjmp (here refl)
  return tt
