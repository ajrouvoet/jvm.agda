{-# OPTIONS --postfix-projections #-}
import MJ.Classtable.Core as Core

module JVM.Syntax.Frames {c}(Ct : Core.Classtable c) where

open import Data.Maybe
open import Data.Maybe.Relation.Unary.Any
open import Data.Maybe.Relation.Unary.All renaming (All to IfJust)
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Binary.Pointwise

open import MJ.Types c
open import MJ.LexicalScope c
open import MJ.Semantics.Values Ct
open Core.Classtable Ct

{- Frames and their typings -}
module _ where

  record FrameTy : Set where
    field
      stack-ty  : List Ty
      locals-ty : List (Maybe Ty)

  record Frame (Φ : FrameTy) (Σ : World) : Set where
    constructor frame
    open FrameTy Φ
    field
      locals : All (Any (Val Σ)) locals-ty
      stack  : All (Val Σ) stack-ty

  open FrameTy public
  open Frame public

{- Subtyping -}
module _ where

  -- extend the sub-type relation to Maybe Ty
  _<∶?_ : Maybe Ty → Maybe Ty → Set
  a? <∶? b? = IfJust (λ b → IfJust (λ a → a <∶⁺ b) a?) b?

  -- extend the sub-type relation to frame typings
  frame_<∶_ : FrameTy → FrameTy → Set
  frame Φ₁ <∶ Φ₂ =
      (Pointwise _<∶?_ (Φ₁ .locals-ty) (Φ₂ .locals-ty))
    × (Pointwise _<∶⁺_ (Φ₁ .stack-ty) (Φ₂ .stack-ty))
