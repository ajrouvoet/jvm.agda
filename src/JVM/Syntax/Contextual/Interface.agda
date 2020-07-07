{-# OPTIONS --safe --no-qualified-instances #-}
module JVM.Defaults.Syntax.Contextual.Interface {ℓ} (T : Set ℓ) where

open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Construct.List.Disjoint T public

LabelCtx = List T

Reference : T → LabelCtx → Set _
Reference ψ I = ψ ∈ I

Binder : T → LabelCtx → Set _
Binder ψ E = ψ ∈ E
