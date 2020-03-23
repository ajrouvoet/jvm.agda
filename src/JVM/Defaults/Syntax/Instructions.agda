{-# OPTIONS --safe #-}
module JVM.Defaults.Syntax.Instructions where

open import JVM.Prelude hiding (swap)
open import Data.List
open import Data.List.Membership.Propositional using () renaming (_∈_ to Reg)

open import JVM.Types
open import JVM.Contexts
open import JVM.Defaults.Syntax.Values

open import Relation.Ternary.Construct.Empty StackTy
open import Relation.Ternary.Construct.Bag empty-rel tt
open import Relation.Ternary.Monad.Weakening

{- Instructions -}
module _ where


  data NativeBinOp : Ty → Ty → Ty → Set where
    add sub mul div xor : NativeBinOp int int int

  data Comparator : List Ty → Set where
    eq ne lt ge gt le : {{Inty a}} → Comparator [ a ]
    icmpge icmpgt icmpeq icmpne icmplt icmple : Comparator (int ∷ int ∷ [])

  -- True to bytecode, the collection of registers is fixed.
  -- The stack typing varies.
  data ⟨_∣_⇒_⟩ (Γ : LocalsTy) : StackTy → StackTy → Pred Labels 0ℓ where
    noop : ε[ ⟨ Γ ∣ ψ ⇒ ψ ⟩ ]

    -- stack manipulation
    pop  :           ε[ ⟨ Γ ∣ a ∷ ψ      ⇒  ψ     ⟩ ]
    push : Const a → ε[ ⟨ Γ ∣ ψ          ⇒  a ∷ ψ ⟩ ]
    dup  : ε[ ⟨ Γ ∣ a ∷ ψ      ⇒  a ∷ a ∷ ψ ⟩ ]
    swap : ε[ ⟨ Γ ∣ a ∷ b ∷ ψ  ⇒  b ∷ a ∷ ψ ⟩ ]

    -- primitive operations
    bop   : NativeBinOp a b c → ε[ ⟨ Γ ∣ a ∷ b ∷ ψ  ⇒  c ∷ ψ ⟩ ]
    new   : ε[ ⟨ Γ ∣ a ∷ ψ ⇒ ref a ∷ ψ ⟩ ]
    read  : ε[ ⟨ Γ ∣ ref a ∷ ψ ⇒ a ∷ ψ ⟩ ]
    write : ε[ ⟨ Γ ∣ a ∷ ref a ∷ ψ ⇒ ψ ⟩ ]

    -- register manipulation
    load  : Reg a Γ → ε[ ⟨ Γ ∣ ψ ⇒ a ∷ ψ ⟩ ]
    store : Reg a Γ → ε[ ⟨ Γ ∣ a ∷ ψ ⇒ ψ ⟩ ]

    -- jumps
    goto  : ∀[ Just ψ₁ ⇒ ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩ ]
    if    : ∀ {as} → Comparator as → ∀[ Just ψ ⇒ ⟨ Γ ∣ as ++ ψ ⇒ ψ ⟩ ]

    -- exceptions/abrupt termination/etc
    ret   : ε[ ⟨ Γ ∣ a ∷ ψ ⇒ ψ ⟩ ]

  -- Compute the stack type after running an instruction.
  -- This is only *not* the same as the stack-type on the rhs for jumps.
  post : ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩ Φ → StackTy
  post {ψ₂ = ψ} noop      = ψ
  post {ψ₂ = ψ} pop       = ψ
  post {ψ₂ = ψ} (push x)  = ψ
  post {ψ₂ = ψ} dup       = ψ
  post {ψ₂ = ψ} swap      = ψ
  post {ψ₂ = ψ} (bop x)   = ψ
  post {ψ₂ = ψ} new       = ψ
  post {ψ₂ = ψ} read      = ψ
  post {ψ₂ = ψ} write     = ψ
  post {ψ₂ = ψ} (load x)  = ψ
  post {ψ₂ = ψ} (store x) = ψ
  post {ψ₂ = ψ} ret       = ψ
  post {ψ₁ = ψ} (goto x)  = ψ
  post {ψ₁ = ψ} (if x x₁) = ψ

module _ τ where
  open import JVM.Defaults.Syntax.Bytecode StackTy ⟨ τ ∣_⇒_⟩ as BC
  open BC using (Code) public

  ⟪_∣_⇐_⟫   = ⟪_⇐_⟫
  ⟪_∣_⇒_⟫   = ⟪_⇒_⟫
  ⟪_∣_⇒_⟫+  = ⟪_⇒_⟫+

module _ {τ} where
  open import JVM.Defaults.Syntax.Bytecode StackTy ⟨ τ ∣_⇒_⟩
    hiding (⟪_⇐_⟫; ⟪_⇒_⟫; ⟪_⇒_⟫+; Code) public
