{-# OPTIONS --safe --no-qualified-instances #-}
open import Data.List hiding (concat)

module JVM.Syntax.Labeling {ℓ} (T : Set ℓ) where

open import Relation.Unary hiding (_∈_; Empty)
open import Relation.Ternary.Core
open import Relation.Ternary.Data.Bigplus

open import Data.Sum
open import Data.Product
 
open import JVM.Model T

Labeling : T → Pred (List T) _
Labeling = λ τ → Bigplus (One τ) 
  where open Disjoint
