module JVM.Types where

open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary

data Ty : Set where
  void : Ty
  int  : Ty
  ref  : Ty → Ty

open import Data.Nat using (ℕ)
NativeBinOp = ℕ → ℕ → ℕ

Ctx : Set
Ctx = List Ty

variable
  a b r s t : Ty
  Γ₁ Γ₂ Γ₃ Γ₄ Γ : Ctx

data Primitive : Ty → Set where
  int  : Primitive int
  void : Primitive void

World : Set
World = List Ty

_≟_ : Decidable (_≡_ {A = Ty})
void ≟ void = yes refl
void ≟ int = no (λ ())
void ≟ ref x = no (λ ())
int ≟ void = no (λ ())
int ≟ int = yes refl
int ≟ ref x = no (λ ())
ref x ≟ void = no (λ ())
ref x ≟ int = no (λ ())
ref x ≟ ref y with x ≟ y
ref x ≟ ref y | yes p = yes (cong ref p)
ref x ≟ ref y | no ¬p = no λ{ refl → ¬p refl }

-- the PRSA for lists of types in general
module _ {a} {A : Set a} where
  open import Relation.Ternary.Core
  open import Relation.Ternary.Structures
  open import Relation.Ternary.Construct.Duplicate A
  open import Relation.Ternary.Construct.List.Interdivide duplicate as LSplit
  open LSplit using (consˡ; consʳ; divide; []) public

  pattern dups s = divide dup s

  instance ctx-rel : Rel₃ _
  ctx-rel = LSplit.splits

  instance ctx-emptiness : Emptiness {A = List A} []
  ctx-emptiness = record {}

  instance ctx-semigroup : IsPartialSemigroup _≡_ LSplit.splits
  ctx-semigroup = LSplit.split-isSemigroup

  instance ctx-monoid : IsPartialMonoid _≡_ LSplit.splits []
  ctx-monoid = LSplit.split-isMonoid
  
  instance ctx-comm : IsCommutative LSplit.splits
  ctx-comm = LSplit.split-isComm

  instance ctx-total : IsTotal LSplit.splits _++_
  ctx-total = LSplit.split-is-total

  dupn : ∀ {xs} → LSplit.Split xs xs xs
  dupn {[]}     = LSplit.[]
  dupn {x ∷ xs} = LSplit.divide dup dupn
