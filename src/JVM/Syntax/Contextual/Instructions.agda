{-# OPTIONS --safe #-}
module JVM.Defaults.Syntax.Contextual.Instructions where

open import Level
open import Data.Unit
open import Data.Product hiding (swap)
open import Data.String using (String)
open import Data.List
open import Data.List.Membership.Propositional

open import JVM.Types
open import JVM.Defaults.Syntax.Values

open import Relation.Unary hiding (_∈_)

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

    noop : ∀[ ⟨ ψ ↝ ψ ⟩ ]

    -- stack manipulation
    pop  :           ∀[ ⟨ a ∷ ψ      ↝  ψ     ⟩ ]
    push : Const a → ∀[ ⟨ ψ          ↝  a ∷ ψ ⟩ ]
    dup  : ∀[ ⟨ a ∷ ψ      ↝  a ∷ a ∷ ψ ⟩ ]
    swap : ∀[ ⟨ a ∷ b ∷ ψ  ↝  b ∷ a ∷ ψ ⟩ ]

    -- binary operations on primitive types
    bop   : NativeBinOp a b c → ∀[ ⟨ a ∷ b ∷ ψ  ↝  c ∷ ψ ⟩ ]

    -- register manipulation
    load  : 𝑹[ a ] → ∀[ ⟨ ψ ↝ a ∷ ψ ⟩ ]
    store : 𝑹[ a ] → ∀[ ⟨ a ∷ ψ ↝ ψ ⟩ ]

    -- jumps
    goto  : ∀[ (ψ₁ ∈_) ⇒ ⟨ ψ₁ ↝ ψ₂ ⟩ ]
    if    : ∀ {as} → Comparator as → ∀[ (ψ ∈_) ⇒ ⟨ as ++ ψ ↝ ψ ⟩ ]

    -- exceptions/abrupt termination/etc
    ret   : ∀[ ⟨ a ∷ ψ₁ ↝ ψ₂ ⟩ ]

  ⟨_∣_↝_⟩ = ⟨_↝_⟩

  open import JVM.Defaults.Syntax.Contextual.Bytecode StackTy ⟨_↝_⟩ public
