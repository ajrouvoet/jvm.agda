module JVM.Defaults.Syntax.Instructions where

open import JVM.Prelude hiding (swap)
open import Data.Bool
open import Data.Sum hiding (swap)
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Binary.Permutation.Inductive hiding (swap)
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Data.Maybe using (just; nothing; Maybe)
open import Relation.Ternary.Monad

open import JVM.Types
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Frames
open import JVM.Defaults.Syntax.Labels

{- Instructions -}
module _ where

  -- True to bytecode, the collection of registers is fixed.
  -- The stack typing varies.
  data ⟨_∣_⇒_⟩ (Γ : LocalsTy) : StackTy → StackTy → Pred Labels 0ℓ where
    noop : ε[ ⟨ Γ ∣ ψ ⇒ ψ ⟩ ]

    -- stack manipulation
    pop  :           ε[ ⟨ Γ ∣ a ∷ ψ      ⇒  ψ     ⟩ ]
    push : Const a → ε[ ⟨ Γ ∣ ψ          ⇒  a ∷ ψ ⟩ ]

    dup  : ε[ ⟨ Γ ∣ a ∷ ψ      ⇒  a ∷ a ∷ ψ ⟩ ]
    swap : ε[ ⟨ Γ ∣ a ∷ b ∷ ψ  ⇒  b ∷ a ∷ ψ ⟩ ]

    -- register manipulation
    load  : a ∈ Γ → ε[ ⟨ Γ ∣ ψ ⇒ a ∷ ψ ⟩ ]
    store : a ∈ Γ → ε[ ⟨ Γ ∣ a ∷ ψ ⇒ ψ ⟩ ]

    -- jumps
    goto  : ∀[ Just ψ ⇒ ⟨ Γ ∣ ψ       ⇒ ψ ⟩ ]
    if    : ∀[ Just ψ ⇒ ⟨ Γ ∣ int ∷ ψ ⇒ ψ ⟩ ]

open import JVM.Defaults.Syntax.Bytecode StackTy public

module _ τ where
  open Codes ⟨ τ ∣_⇒_⟩

  ⟪_∣_⇒_⟫   = ⟪_⇒_⟫
  ⟪_∣_⇒_⟫+  = ⟪_⇒_⟫+
  ⟪_∣_⇒_⇒_⟫ = Zipper

module _ {τ} where
  open Codes ⟨ τ ∣_⇒_⟩
    hiding (⟪_⇒_⟫; ⟪_⇒_⟫+; Zipper; Code) public
