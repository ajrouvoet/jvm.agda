import MJ.Classtable.Core as Core

module JVM.Defaults.Syntax.Bytecode {c}(Ct : Core.Classtable c) where

open import Prelude hiding (swap)
open import Data.Bool
open import Data.Sum hiding (swap)
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Binary.Permutation.Inductive hiding (swap)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Data.Maybe using (just; nothing; Maybe)

open import MJ.Types c
open import JVM.Defaults.Syntax.Frames Ct

open import Data.List.Membership.Propositional {A = RegTy}

module _ where

  Labels  = List StackTy

  -- The PRSA for Labels
  open import Relation.Ternary.Construct.Duplicate StackTy as Dup
  open import Relation.Ternary.Construct.List.Intermuted StackTy
    Dup.dup-rel isCommSemigroup public

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

open import Relation.Ternary.Construct.Exchange {A = Labels} _↭_ as Exchange
  renaming (Account to Intf) public

{- Bytecode; i.e., instruction sequences -}
module _ where

  open import Relation.Ternary.Data.ReflexiveTransitive {C = Intf} isCommMonoid public

  data Code (Γ : LocalsTy) : StackTy → StackTy → Pred Intf 0ℓ where
    label : ∀[ ● (Just ψ)       ⇒ Code Γ ψ ψ ]
    instr : ∀[ ○ ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩ ⇒ Code Γ ψ₁ ψ₂ ]

  ⟪_∣_⇒_⟫ : LocalsTy → StackTy → StackTy → Pred Intf 0ℓ
  ⟪ Γ ∣ ψ₁ ⇒ ψ₂ ⟫ = Star (Code Γ) ψ₁ ψ₂

  -- another representation where every instruction can have at most one label:

  -- Label? : StackTy → Pred Intf 0ℓ
  -- Label? ψ = ● (Just ψ) ∪ Emp

  -- Code = λ Γ ψ₁ ψ₂ → Label? ψ₁ ✴ ○ ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩

  -- ⟪_∣_⇒_⟫ : LocalsTy → StackTy → StackTy → Pred Intf 0ℓ
  -- ⟪ Γ ∣ ψ₁ ⇒ ψ₂ ⟫ = Star (Code Γ) ψ₁ ψ₂
