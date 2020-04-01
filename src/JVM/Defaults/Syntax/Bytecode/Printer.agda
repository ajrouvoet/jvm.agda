{-# OPTIONS --no-qualified-instances #-}
open import Data.List
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

import JVM.Defaults.Printer.Printer as Printer
import JVM.Model as Model

module JVM.Defaults.Syntax.Bytecode.Printer {ℓ T}
  (⟨_⇒_⟩ : T → T → List T → Set ℓ)
  (let open Model T)
  (let open Printer T)
  (print : ∀ {τ₁ τ₂} → ∀[ Down ⟨ τ₁ ⇒ τ₂ ⟩ ⇒ Printer Emp ] ) where

open import JVM.Defaults.Syntax.Bytecode T ⟨_⇒_⟩
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Data.ReflexiveTransitive
open import Relation.Ternary.Monad

{-# TERMINATING #-}
pretty : ∀ {ψ₁ ψ₂} → ∀[ ⟪ ψ₁ ⇒ ψ₂ ⟫ ⇒ Printer Emp ]
pretty nil      = do
  return refl
pretty (instr i   ▹⟨ σ ⟩ is) = do
  is          ← ✴-id⁻ʳ ⟨$⟩ (print i &⟨ ⟪ _ ⇒ _ ⟫ # ∙-comm σ ⟩ is)
  pretty is
pretty (labeled l∙i ▹⟨ σ₂ ⟩ is) = do
  let l ∙⟨ σ ⟩ i∙is = ✴-assocᵣ (l∙i ∙⟨ σ₂ ⟩ is)
  i ∙⟨ σ ⟩ is       ← ✴-id⁻ʳ ⟨$⟩ (print-labels l &⟨ _ ✴ ⟪ _ ⇒ _ ⟫ # ∙-comm σ ⟩ i∙is)
  is                ← ✴-id⁻ʳ ⟨$⟩ (print i        &⟨                 ∙-comm σ ⟩ is)
  pretty is
