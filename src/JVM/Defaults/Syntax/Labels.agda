import MJ.Classtable.Core as Core

module JVM.Defaults.Syntax.Labels {c}(Ct : Core.Classtable c) where

open import Data.List
open import JVM.Defaults.Syntax.Frames Ct

Labels  = List StackTy

variable
  ι₁ ι₂ ι₃ ι : Labels

open import Relation.Ternary.Construct.GlobalBinding StackTy public
