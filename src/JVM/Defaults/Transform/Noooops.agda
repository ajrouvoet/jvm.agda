{- Noop removal transformation on bytecode -}
import MJ.Classtable.Core as Core

module JVM.Defaults.Transform.Noooops {c}(Ct : Core.Classtable c) where

open import JVM.Prelude hiding (swap; ↑_)
open import Data.List.Relation.Binary.Permutation.Inductive hiding (swap)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Data.Maybe using (just; nothing; Maybe)

open import MJ.Types c
open import JVM.Defaults.Syntax.Frames Ct
open import JVM.Defaults.Syntax.Labels Ct
open import JVM.Defaults.Syntax.Bytecode Ct

is-noop : (i : ⟨ τ ∣ ψ₁ ⇒ ψ₂ ⟩ Φ) → Maybe (ψ₁ ≡ ψ₂ × Φ ≡ ε)
is-noop noop = just (refl , refl)
is-noop _    = nothing

noooop : ∀[ ⟪ τ ∣ ψ₁ ⇒ ψ₂ ⟫ ⇒ ⟪ τ ∣ ψ₁ ⇒ ψ₂ ⟫ ]
noooop nil                               = nil
noooop (cons (label (↑ refl) ×⟨ σ ⟩ is)) = cons (label (↑ refl) ×⟨ σ ⟩ noooop is)
noooop (cons (instr (↓ i)    ×⟨ σ ⟩ is)) with is-noop i
... | just (refl , refl) = coe (∙-id⁻ˡ σ) (noooop is)
... | nothing = cons (instr (↓ i) ×⟨ σ ⟩ noooop is)

