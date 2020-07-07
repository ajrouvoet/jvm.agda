{-# OPTIONS --safe #-}
module JVM.Syntax.Values where

open import Level
open import Data.Bool
open import Data.Nat
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

open import JVM.Types

data Const : Ty → Set where
  null : ∀ {c} → Const (ref c)
  num  : ℕ     → Const int
  bool : Bool  → Const boolean
