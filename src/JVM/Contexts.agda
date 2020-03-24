-- {-# OPTIONS --safe #-}
module JVM.Contexts where

open import Data.Product
open import JVM.Types
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

-- Typings of register files make good lexical contexts
open import Relation.Ternary.Construct.List.Overlapping Ty public
  renaming
    ( overlap-rel to ctx-rel
    ; overlap-commutative to ctx-commutative
    ; overlap-semigroup to ctx-semigroup
    ; overlap-monoid to ctx-monoid)

data Globals : Set where

abstract
  ICtx  = Globals × Labels

iPred = ICtx → Set

abstract
  postulate Lbl : StackTy → iPred

  private
    postulate unit : ICtx

  instance ictx-empty : Emptiness {A = ICtx} unit
  ictx-empty = record {}

  postulate _≈ictx≈_ : ICtx → ICtx → Set
  postulate instance ictxs : Rel₃ ICtx
  postulate instance ictx-semigroup : IsPartialSemigroup _≈ictx≈_ ictxs
  postulate instance ictx-monoid : IsPartialMonoid _≈ictx≈_ ictxs unit
