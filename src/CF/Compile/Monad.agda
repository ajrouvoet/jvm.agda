open import Data.List

module CF.Compile.Monad (T : Set) (⟨_⇒_⟩ : T → T → List T → Set) where

open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad

private
  variable
    τ₁ τ₂ τ : T

open import JVM.Model T; open Syntax
open import JVM.Defaults.Syntax.Bytecode T ⟨_⇒_⟩

Compiler : T → T → Pt Intf 0ℓ
Compiler ψ₁ ψ₂ P = ⟪ ψ₁ ⇒ ψ₂ ⟫ ⊙ P

postulate tell        : ∀[ Down ⟨ τ₁ ⇒ τ₂ ⟩ ⇒ Compiler τ₁ τ₂ Emp ] 
postulate mklabel     : ε[ Compiler τ₁ τ₁ (Up (Just τ) ⊙ Down (Just τ)) ]
postulate label-start : ∀ {P} → ∀[ Up (Just τ₁) ⇒ Compiler τ₁ τ₂ P ─⊙ Compiler τ₁ τ₂ P ]

postulate instance compiler-monad : Monad T Compiler

open Monad compiler-monad public
open Bind     {{pm = intf-isMonoid}} {{monad = compiler-monad}} {{ ⊙-respect-≈ }} public
open Strength {{monad = compiler-monad}} public
