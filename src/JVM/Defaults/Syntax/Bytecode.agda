import MJ.Classtable.Core as Core

module JVM.Defaults.Syntax.Bytecode {c}(Ct : Core.Classtable c) where

open import Level
open import Function using (const)
open import Data.Bool
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Binary.Permutation.Propositional
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Separation

open import MJ.Types c
open import MJ.LexicalScope c
open import JVM.Defaults.Syntax.Frames Ct
open import Data.List.Membership.Propositional {A = RegTy}

module _ where

  Labels  = List StackTy

  -- The PRSA for Labels
  open import Relation.Ternary.Separation.Construct.Duplicate as Dup
  open import Relation.Ternary.Separation.Construct.List.Intermuted StackTy
    (Dup.dup-sep StackTy) {{Dup.dup-is-sep StackTy}} public

{- Instructions -}
module _ where

  -- True to bytecode, the collection of registers is fixed.
  -- The stack typing varies.
  data ⟨_∣_⇒_⟩ (Γ : LocalsTy) : StackTy → StackTy → Pred Labels 0ℓ where

    -- stack manipulation
    pop  : ε[ ⟨ Γ ∣ a ∷ ψ      ⇒  ψ         ⟩ ]
    push : ε[ ⟨ Γ ∣ ψ          ⇒  a ∷ ψ     ⟩ ]
    dup  : ε[ ⟨ Γ ∣ a ∷ ψ      ⇒  a ∷ a ∷ ψ ⟩ ]
    swap : ε[ ⟨ Γ ∣ a ∷ b ∷ ψ  ⇒  b ∷ a ∷ ψ ⟩ ]

    -- register manipulation
    load  : a ∈ Γ → ∀[ ⟨ Γ ∣ ψ ⇒ a ∷ ψ ⟩ ]
    store : a ∈ Γ → ∀[ ⟨ Γ ∣ a ∷ ψ ⇒ ψ ⟩ ]

    -- jumps
    goto  : ∀[ Just ψ ⇒ ⟨ Γ ∣ ψ ⇒ ψ       ⟩ ]
    if    : ∀[ Just ψ ⇒ ⟨ Γ ∣ int ∷ ψ ⇒ ψ ⟩ ]

open import Relation.Ternary.Separation.Construct.Exchange {A = Labels} _↭_
  public
  renaming (Account to Intf)
open import Relation.Ternary.Separation.Monad (record { isEquivalence = account-equiv })
open import Relation.Ternary.Separation.Monad.Quotient

{- Instruction sequences -}
module _ where

  data Label (ψ : StackTy) : Pred Intf 0ℓ where
    label : Label ψ ([ ψ ] ↕ ε)

  -- reflexive transitive closure of ⟨_⇒_⟩, plus labels
  data ⟪_∣_⇒_⟫ (Γ : LocalsTy) : (ψ₁ ψ₂ : StackTy) → Pred Intf 0ℓ where
    block : ε[ ⟪ Γ ∣ ψ₁ ⇒ ψ₁ ⟫ ]
    cons  : ∀[ (Label ψ₁ ✴ ○ ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩) ✴ ⟪ Γ ∣ ψ₂ ⇒ ψ₃ ⟫ ⇒ ⟪ Γ ∣ ψ₁ ⇒ ψ₃ ⟫ ]

  pattern _;⟨_⟩_ li σ b = cons (li ×⟨ σ ⟩ b)

  seq : ∀[ ⟪ Γ ∣ ψ₁ ⇒ ψ₂ ⟫ ⇒ ⟪ Γ ∣ ψ₂ ⇒ ψ₃ ⟫ ~✴ ⟪ Γ ∣ ψ₁ ⇒ ψ₃ ⟫ ]
  seq block    ⟨ σ₂ ⟩ b₂ = b₂ div (⊎-id⁻ˡ σ₂)
  seq (li ;⟨ σ₁ ⟩ b₁) ⟨ σ₂ ⟩ b₂ = do
    let _ , τ₁ , τ₂ = ⊎-assoc σ₁ σ₂
    b₃ ×⟨ σ₃ ⟩ li ← seq b₁ ⟨ τ₂ ⟩ b₂ &⟨ ⊎-comm τ₁ ⟩ li
    return (li ;⟨ ⊎-comm σ₃ ⟩ b₃)
