module JVM.Defaults.Syntax.Labels where

open import Data.List
open import JVM.Defaults.Syntax.Frames

Labels  = List StackTy

variable
  ι₁ ι₂ ι₃ ι : Labels

open import Relation.Ternary.Construct.GlobalBinding StackTy public
