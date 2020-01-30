import MJ.Classtable.Core as Core

module JVM.Defaults.Syntax.Frames {c}(Ct : Core.Classtable c) where

open import Data.List.Relation.Unary.All
open import Data.List.Relation.Binary.Pointwise
open import Relation.Ternary.Separation
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Structures

open import MJ.Types c
open Core.Classtable Ct
open import JVM.Prelude

-- the PRSA for lists of types in general
module _ {a} {A : Set a} where
  open import Relation.Ternary.Construct.Duplicate A
  open import Relation.Ternary.Construct.List.Interdivide duplicate as LSplit

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

  dupn : ∀ {xs} → LSplit.Split xs xs xs
  dupn {[]}     = LSplit.[]
  dupn {x ∷ xs} = LSplit.divide dup dupn
  
{- Frames and their typings -}
module _ where

  RegTy    = Ty
  StackTy  = List Ty
  LocalsTy = List RegTy

  variable
    ψ₁ ψ₂ ψ₃ ψ : StackTy  -- stack typings
    τ₁ τ₂ τ₃ τ : LocalsTy -- register file typings

  record FrameTy : Set where
    constructor ⟨_,_⟩
    field
      locals-ty : List RegTy
      stack-ty  : List Ty
