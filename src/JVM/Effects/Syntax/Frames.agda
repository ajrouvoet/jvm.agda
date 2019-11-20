{-# OPTIONS --postfix-projections #-}
import MJ.Classtable.Core as Core

module JVM.Syntax.Frames {c}(Ct : Core.Classtable c) where

open import Data.Bool
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

  -- register typings are pairs of value types with
  -- a flag indicating initialization status
  RegTy = Ty × Bool

  pattern init a  = _,_ a true 
  pattern uninit a = _,_ a false

  StackTy  = List Ty
  LocalsTy = List RegTy

  -- the PRSA for LocalsTy
  open import Relation.Ternary.Separation.Construct.Duplicate as Dup
  open import Relation.Ternary.Separation.Construct.List.Interdivide RegTy
    (Dup.dup-sep RegTy) {{Dup.dup-is-sep RegTy}} public

  variable
    ψ₁ ψ₂ ψ : StackTy  -- stack typings
    τ₁ τ₂ τ : LocalsTy -- register file typings

  infixl 1 _∣_
  record FrameTy : Set where
    constructor _∣_
    field
      locals-ty : List RegTy
      stack-ty  : List Ty

  record Frame (ft : FrameTy) (Σ : World) : Set where
    constructor frame
    open FrameTy ft
    field
      locals : All (λ where (a , i) → if i then (Val Σ a) else ⊤ ) locals-ty
      stack  : All (Val Σ) stack-ty

  variable
    ft₁ ft₂ ft₃ ft₄ ft : FrameTy

  open FrameTy public
  open Frame public

{- Subtyping -}
module _ where

  data IfInited (P : Ty → Set) : RegTy → Set where
    jep  : P a → IfInited P (a , true)
    nope : IfInited P (a , false)

  data Inited (P : Ty → Set) : RegTy → Set where
    jep  : P a → Inited P (a , true)

  -- Extend the sub-type relation to register typings.
  _<∶?_ : RegTy → RegTy → Set
  a? <∶? b? = IfInited (λ b → Inited (λ a → a <∶⁺ b) a?) b?

  -- extend the sub-type relation to frame typings
  frame_<∶_ : FrameTy → FrameTy → Set
  frame ft₁ <∶ ft₂ =
      (Pointwise _<∶?_ (ft₁ .locals-ty) (ft₂ .locals-ty))
    × (Pointwise _<∶⁺_ (ft₁ .stack-ty) (ft₂ .stack-ty))
