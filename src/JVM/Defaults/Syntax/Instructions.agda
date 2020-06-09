{-# OPTIONS --safe #-}
module JVM.Defaults.Syntax.Instructions where

open import Level
open import Data.Unit
open import Data.Product hiding (swap)
open import Data.String using (String)
open import Data.List
open import Data.List.Membership.Propositional using () renaming (_∈_ to Reg)

open import JVM.Types
open import JVM.Defaults.Syntax.Values

open import Relation.Unary hiding (_∈_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Construct.Empty StackTy
open import Relation.Ternary.Construct.Bag empty-rel tt
open import Relation.Ternary.Monad.Weakening

data NativeBinOp : Ty → Ty → Ty → Set where
  add sub mul div xor : NativeBinOp int int int

data Comparator : List Ty → Set where
  eq ne lt ge gt le : {{IsIntegral a}} → Comparator [ a ]
  icmpge icmpgt icmpeq icmpne icmplt icmple : Comparator (int ∷ [ int ])

{- Instructions -}
module _ (𝑭 : FrameTy) where

  open import Data.List.Membership.Propositional

  𝑪[_] : Constant → Set
  𝑪[ κ ] = κ ∈ (proj₁ 𝑭)

  𝑹[_] : Ty → Set
  𝑹[ a ] = a ∈ (proj₂ 𝑭)

  open Fld
  open Fun

  -- True to bytecode, the collection of registers is fixed.
  -- The stack typing varies.
  data ⟨_↝_⟩ : StackTy → StackTy → Pred Labels 0ℓ where

    noop : ε[ ⟨ ψ ↝ ψ ⟩ ]

    -- stack manipulation
    pop  :           ε[ ⟨ a ∷ ψ      ↝  ψ     ⟩ ]
    push : Const a → ε[ ⟨ ψ          ↝  a ∷ ψ ⟩ ]
    dup  : ε[ ⟨ a ∷ ψ      ↝  a ∷ a ∷ ψ ⟩ ]
    swap : ε[ ⟨ a ∷ b ∷ ψ  ↝  b ∷ a ∷ ψ ⟩ ]

    -- binary operations on primitive types
    bop   : NativeBinOp a b c → ε[ ⟨ a ∷ b ∷ ψ  ↝  c ∷ ψ ⟩ ]

    -- register manipulation
    load  : 𝑹[ a ] → ε[ ⟨ ψ ↝ a ∷ ψ ⟩ ]
    store : 𝑹[ a ] → ε[ ⟨ a ∷ ψ ↝ ψ ⟩ ]

    -- jumps
    goto  : ∀[ One ψ₁ ⇒ ⟨ ψ₁ ↝ ψ₂ ⟩ ]
    if    : ∀ {as} → Comparator as → ∀[ One ψ ⇒ ⟨ as ++ ψ ↝ ψ ⟩ ]

    -- exceptions/abrupt termination/etc
    ret   : ε[ ⟨ a ∷ ψ₁ ↝ ψ₂ ⟩ ]

    -- member access
    -- getstatic : 𝑪[ staticref 𝑎 ] → ε[ ⟨ ψ ↝ fld 𝑎 ty ∷ ψ ⟩ ]
    -- getfield  : 𝑪[ fieldref 𝑎  ] → ε[ ⟨ ref (fld 𝑎 cls) ∷ ψ ↝ fld 𝑎 ty ∷ ψ ⟩ ]
    -- putfield  : 𝑪[ fieldref 𝑎  ] → ε[ ⟨ fld 𝑎 ty ∷ ref (fld 𝑎 cls) ∷ ψ ↝ ψ ⟩ ]
    -- new       : 𝑪[ class 𝑐     ] → ε[ ⟨ ψ ↝ ref 𝑐 ∷ ψ ⟩ ]

    -- calls
    -- invokestatic  : ∀ {as r} → 𝑪[ staticfun (𝑐 / 𝑚 :⟨ as ⟩ r) ] → ε[ ⟨ (as ++ ψ)         ↝ r :?: ψ ⟩ ]
    -- invokespecial : ∀ {as r} → 𝑪[ virtual   (𝑐 / 𝑚 :⟨ as ⟩ r) ] → ε[ ⟨ (ref 𝑐 ∷ as ++ ψ) ↝ r :?: ψ ⟩ ]
    -- invokevirtual : ∀ {as r} → 𝑪[ virtual   (𝑐 / 𝑚 :⟨ as ⟩ r) ] → ε[ ⟨ (ref 𝑐 ∷ as ++ ψ) ↝ r :?: ψ ⟩ ]

  ⟨_∣_↝_⟩ = ⟨_↝_⟩

  open import JVM.Defaults.Syntax.Bytecode StackTy ⟨_↝_⟩ as BC
  open BC using (Code) public

  ⟪_∣_↜_⟫   = ⟪_↜_⟫
  ⟪_∣_↝_⟫   = ⟪_↝_⟫
  ⟪_∣_↝_⟫+  = ⟪_↝_⟫+

module _ {𝑭} where
  open import JVM.Defaults.Syntax.Bytecode StackTy ⟨ 𝑭 ∣_↝_⟩
    hiding (⟪_↜_⟫; ⟪_↝_⟫; ⟪_↝_⟫+; Code) public

-- Compute the stack type after running an instruction.
-- This is only *not* the same as the stack-type on the rhs for jumps.
-- post : ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩ Φ → StackTy
-- post {ψ₂ = ψ} noop      = ψ
-- post {ψ₂ = ψ} pop       = ψ
-- post {ψ₂ = ψ} (push x)  = ψ
-- post {ψ₂ = ψ} dup       = ψ
-- post {ψ₂ = ψ} swap      = ψ
-- post {ψ₂ = ψ} (bop x)   = ψ
-- post {ψ₂ = ψ} new       = ψ
-- post {ψ₂ = ψ} (load x)  = ψ
-- post {ψ₂ = ψ} (store x) = ψ
-- post {ψ₂ = ψ} ret       = ψ
-- post {ψ₁ = ψ} (goto x)  = ψ
-- post {ψ₁ = ψ} (if x x₁) = ψ
