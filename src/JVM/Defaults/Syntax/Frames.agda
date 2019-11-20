{-# OPTIONS --postfix-projections #-}
import MJ.Classtable.Core as Core

module JVM.Defaults.Syntax.Frames {c}(Ct : Core.Classtable c) where

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

  RegTy    = Ty
  StackTy  = List Ty
  LocalsTy = List RegTy

  -- the PRSA for LocalsTy
  open import Relation.Ternary.Separation.Construct.Duplicate as Dup
  open import Relation.Ternary.Separation.Construct.List.Interdivide RegTy
    (Dup.dup-sep RegTy) {{Dup.dup-is-sep RegTy}} public

  variable
    ψ₁ ψ₂ ψ₃ ψ : StackTy  -- stack typings
    τ₁ τ₂ τ₃ τ : LocalsTy -- register file typings

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
      locals : All (Val Σ) locals-ty
      stack  : All (Val Σ) stack-ty

  variable
    ft₁ ft₂ ft₃ ft₄ ft : FrameTy

  open FrameTy public
  open Frame public
