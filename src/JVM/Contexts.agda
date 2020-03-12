{-# OPTIONS --safe #-}
module JVM.Contexts where

open import JVM.Types

open import Relation.Ternary.Construct.List.Overlapping Ty public
  renaming
    ( overlap-rel to ctx-rel
    ; overlap-commutative to ctx-commutative
    ; overlap-semigroup to ctx-semigroup
    ; overlap-monoid to ctx-monoid)
