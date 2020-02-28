{- Noop removal transformation on bytecode -}
module JVM.Defaults.Transform.Noooops where

open import JVM.Prelude hiding (swap; ↑_)
open import Data.List.Relation.Binary.Permutation.Inductive hiding (swap)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Data.ReflexiveTransitive

open import JVM.Types
open import JVM.Defaults.Syntax.Instructions
open import JVM.Defaults.Syntax.Bytecode

open import Relation.Ternary.Construct.GlobalBinding StackTy
open import Data.Maybe using (just; nothing; Maybe)

is-noop : (i : ⟨ τ ∣ ψ₁ ⇒ ψ₂ ⟩ Φ) → Maybe (ψ₁ ≡ ψ₂ × Φ ≡ ε)
is-noop noop = just (refl , refl)
is-noop _    = nothing

noooop : ∀[ ⟪ τ ∣ ψ₁ ⇒ ψ₂ ⟫ ⇒ ⟪ τ ∣ ψ₁ ⇒ ψ₂ ⟫ ]
noooop nil = nil

-- (1) not labeled
noooop (instr (↓ i) ▹⟨ σ ⟩ is) with is-noop i
--   (a) not noop: keep
... | nothing            = instr (↓ i) ▹⟨ σ ⟩ noooop is
--   (b) noop: drop
... | just (refl , refl) = coe (∙-id⁻ˡ σ) is

-- (2) is labeled
noooop (li@(labeled (l ∙⟨ σ₀ ⟩ ↓ i)) ▹⟨ σ ⟩ is) with is-noop i

--   (a) not noop: keep
... | nothing = li ▹⟨ σ ⟩ noooop is

--   (b) noop
... | just (refl , refl) with noooop is
--      (*) tail empty, keep
... | nil = li ▹⟨ σ ⟩ nil
--      (*) tail occupied, drop and merge labels
... | j ▹⟨ σ′ ⟩ js with ∙-assocₗ σ σ′
... | _ , σ₃ , σ₄ =
  (label l ⟨ coe {{∙-respects-≈ˡ}} (sym (∙-id⁻ʳ σ₀)) σ₃ ⟩ j) ▹⟨ σ₄ ⟩ js 
