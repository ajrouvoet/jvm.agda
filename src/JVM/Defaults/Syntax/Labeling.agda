{-# OPTIONS --safe --no-qualified-instances #-}
-- Bytecode; i.e., instruction sequences; 
-- agnostic about the exact instructions, but opiniated about labels
open import Data.List hiding (concat)

module JVM.Defaults.Syntax.Labeling {ℓ} (T : Set ℓ) where

open import Relation.Unary hiding (_∈_; Empty)
open import Relation.Ternary.Core
open import Relation.Ternary.Data.Bigstar

open import Data.Sum
open import Data.Product
 
open import JVM.Model T
open Disjoint

Labels = List T

Labeling : T → Pred (List T) _
Labeling = λ τ → Bigstar (One τ) 
