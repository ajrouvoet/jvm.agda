{-# OPTIONS --rewriting #-}
module CF.Transform.Compile.ToJVM.Rewriting where

open import Data.List.Properties
open import Data.List.Relation.Binary.Permutation.Propositional

open import Agda.Builtin.Equality.Rewrite

{-# REWRITE map-++-commute #-}

