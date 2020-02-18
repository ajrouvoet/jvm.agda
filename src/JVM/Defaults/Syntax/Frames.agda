module JVM.Defaults.Syntax.Frames where

open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Binary.Pointwise
open import Relation.Ternary.Separation
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Structures

open import JVM.Types
open import JVM.Prelude
  
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
