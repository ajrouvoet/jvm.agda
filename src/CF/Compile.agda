module CF.Compile where

open import Data.List
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import CF.Syntax

open import JVM.Types
open import JVM.Defaults.Syntax.Frames
open import JVM.Defaults.Syntax.Instructions

compileₑ : ∀ {ψ : StackTy} → Exp a Γ → ε[ ⟪ Γ ∣ ψ ⇒ (a ∷ ψ) ⟫ ]
compileₑ e = {!!}
