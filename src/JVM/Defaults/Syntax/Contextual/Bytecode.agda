{-# OPTIONS --safe --no-qualified-instances #-}
open import Data.List hiding (concat)

module JVM.Defaults.Syntax.Contextual.Bytecode {ℓ} (T : Set ℓ) (Instr : T → T → List T → Set ℓ) where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Relation.Unary hiding (_∈_; Empty)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Data.ReflexiveTransitive as Star
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Data.Bigstar
open import Relation.Ternary.Data.IndexedMonoid

open import JVM.Defaults.Syntax.Contextual.Interface T

open import Data.Sum
open import Data.Product

open import JVM.Defaults.Syntax.Labeling T public

data Code (I : LabelCtx) : T → T → Pred LabelCtx ℓ where
  instr   : ∀ {τ₁ τ₂} → Instr τ₁ τ₂ I → ε[ Code I τ₁ τ₂ ]
  labeled : ∀ {τ₁ τ₂} → Instr τ₁ τ₂ I → ∀[ Labeling τ₁ ⇒ Code I τ₁ τ₂ ]

Bytecode : LabelCtx → T → T → Pred LabelCtx ℓ
Bytecode I = Star (Code I)
