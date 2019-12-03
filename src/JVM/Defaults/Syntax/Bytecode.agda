import MJ.Classtable.Core as Core

module JVM.Defaults.Syntax.Bytecode {c}(Ct : Core.Classtable c) where

open import Prelude hiding (swap)
open import Function using (const)
open import Data.Bool
open import Data.Sum hiding (swap)
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Binary.Permutation.Inductive hiding (swap)
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Data.Maybe using (just; nothing; Maybe)

open import MJ.Types c
open import JVM.Defaults.Syntax.Frames Ct
open import Data.List.Membership.Propositional {A = RegTy}

module _ where

  Labels  = List StackTy

  -- The PRSA for Labels
  open import Relation.Ternary.Construct.Duplicate StackTy as Dup
  open import Relation.Ternary.Construct.List.Intermuted StackTy
    Dup.dup-sep isCommSemigroup public

{- Instructions -}
module _ where

  -- True to bytecode, the collection of registers is fixed.
  -- The stack typing varies.
  data ⟨_∣_⇒_⟩ (Γ : LocalsTy) : StackTy → StackTy → Pred Labels 0ℓ where
    noop : ε[ ⟨ Γ ∣ ψ ⇒ ψ ⟩ ]

    -- stack manipulation
    pop  : ε[ ⟨ Γ ∣ a ∷ ψ      ⇒  ψ         ⟩ ]
    push : ε[ ⟨ Γ ∣ ψ          ⇒  a ∷ ψ     ⟩ ]
    dup  : ε[ ⟨ Γ ∣ a ∷ ψ      ⇒  a ∷ a ∷ ψ ⟩ ]
    swap : ε[ ⟨ Γ ∣ a ∷ b ∷ ψ  ⇒  b ∷ a ∷ ψ ⟩ ]

    -- register manipulation
    load  : a ∈ Γ → ε[ ⟨ Γ ∣ ψ ⇒ a ∷ ψ ⟩ ]
    store : a ∈ Γ → ε[ ⟨ Γ ∣ a ∷ ψ ⇒ ψ ⟩ ]

    -- jumps
    goto  : ∀[ Just ψ ⇒ ⟨ Γ ∣ ψ ⇒ ψ       ⟩ ]
    if    : ∀[ Just ψ ⇒ ⟨ Γ ∣ int ∷ ψ ⇒ ψ ⟩ ]

open import Relation.Ternary.Construct.Exchange {A = Labels} _↭_
  as Exchange
  public renaming (Account to Intf)
open import Relation.Ternary.Monad
open import Relation.Binary.Structures
open IsEquivalence {{...}} using ()
  renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

{- Bytecode; i.e., instruction sequences -}
module _ where

  open import Relation.Ternary.Data.ReflexiveTransitive public

  Label? : StackTy → Pred Intf 0ℓ
  Label? ψ = ● (Just ψ) ∪ Emp

  Code = λ Γ ψ₁ ψ₂ → Label? ψ₁ ✴ ○ ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩

  ⟪_∣_⇒_⟫ : LocalsTy → StackTy → StackTy → Pred Intf 0ℓ
  ⟪ Γ ∣ ψ₁ ⇒ ψ₂ ⟫ = Star (Code Γ) ψ₁ ψ₂

-- {- Noop removal transformation on bytecode -}
-- module _ where

--   is-noop : (i : ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩ Φ) → Maybe (ψ₁ ≡ ψ₂ × Φ ≡ ε)
--   is-noop noop = just (refl , refl)
--   is-noop _    = nothing

--   noooop : ∀[ ⟪ Γ ∣ ψ₁ ⇒ ψ₂ ⟫ ≈> ⟪ Γ ∣ ψ₁ ⇒ ψ₂ ⟫ ]
--   noooop nil = return nil

--   -- first we test if the instruction is a noop at all:
--   -- if not, we leave it as a whole and recursively proceed on the tail.
--   noooop (h@(l? ×⟨ σ ⟩ ↓ i) ▹⟨ σ₂ ⟩ tail) with is-noop i
--   ... | nothing = do
--     tail ×⟨ σ₃ ⟩ h ← noooop tail &⟨ ⊎-comm σ₂ ⟩ h
--     return (h ▹⟨ ⊎-comm σ₃ ⟩ tail)

--   -- if it *is* a noop, then we have to test if it is labeled:
--   ... | just (refl , refl) with l?

--   -- it is labeled:
--   ... | inj₁ (↑ refl) = do
--     tail ← noooop tail 
--     ?

--   -- it is not labeled:
--   ... | inj₂ empty with ε⊎ε σ
--   ... | refl = coe (⊎-id⁻ˡ σ₂) (noooop tail)
