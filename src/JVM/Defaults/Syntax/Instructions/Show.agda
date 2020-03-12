module JVM.Defaults.Syntax.Instructions.Show where

open import Data.String as String hiding (show)
open import Data.Nat.Show as Nat hiding (show)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad.Weakening
open import Relation.Ternary.Data.ReflexiveTransitive

open import JVM.Types
open import JVM.Contexts
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions
open import JVM.Model using (↑; ↓)

show-instr : ∀ {Φ} → ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩ Φ → String
show-instr noop      = "noop"
show-instr pop       = "pop"
show-instr (push x)  = "push"
  where
    show-const : Const a → String
    show-const null    = "null"
    show-const unit    = "unit"
    show-const (num x) = Nat.show x
show-instr dup       = "dup"
show-instr swap      = "swap"
show-instr (bop x)   = "bop"
show-instr new       = "new"
show-instr read      = "read"
show-instr write     = "write"
show-instr (load (refl ⇈ wk))  = "load "  ++ Nat.show (indexOf wk)
show-instr (store (refl ⇈ wk)) = "store " ++ Nat.show (indexOf wk)
show-instr (goto x)  = "goto"
show-instr (if c x₁) = "if" ++ show-comp c
  where
    show-comp : Comparator → String
    show-comp eq = "eq"
    show-comp ne = "ne"
    show-comp lt = "lt"
    show-comp ge = "ge"
    show-comp gt = "gt"
    show-comp le = "le"
show-instr ret       = "ret"

module _ {Γ} where
  open import JVM.Defaults.Syntax.Bytecode _ ⟨ Γ ∣_⇒_⟩

  show-code : ∀ {Φ} → Code ψ₁ ψ₂ Φ → String
  show-code (labeled (_ ∙⟨ _ ⟩ ↓ i))   = "<>: " ++ show-instr i
  show-code (instr (↓ i))              = "    " ++ show-instr i

show : ∀ {Φ} → ⟪ Γ ∣ ψ₁ ⇒ ψ₂ ⟫ Φ → String
show nil      = ""
show (c ▹⟨ σ ⟩ is) = show-code c ++ "\n" ++ show is
