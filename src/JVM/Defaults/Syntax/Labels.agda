import MJ.Classtable.Core as Core

module JVM.Defaults.Syntax.Labels {c}(Ct : Core.Classtable c) where

open import JVM.Prelude
open import JVM.Defaults.Syntax.Frames Ct

Labels  = List StackTy

variable
  ι₁ ι₂ ι₃ ι : Labels

-- The PRSA for Labels
open import Relation.Ternary.Construct.Duplicate StackTy as Dup
open import Relation.Ternary.Construct.List.Intermuted StackTy
  Dup.duplicate isCommSemigroup public
