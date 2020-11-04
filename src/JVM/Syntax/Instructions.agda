{-# OPTIONS --safe --no-qualified-instances #-}
module JVM.Syntax.Instructions where

open import Level
open import Data.Unit
open import Data.Product hiding (swap)
open import Data.String using (String)
open import Data.List
open import Data.List.Membership.Propositional using () renaming (_∈_ to Reg)

open import JVM.Types
open import JVM.Syntax.Values
open import JVM.Model StackTy

open import Relation.Unary hiding (_∈_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad.Weakening

data NativeBinOp : Ty → Ty → Ty → Set where
  add sub mul div xor : NativeBinOp int int int

data Comparator : List Ty → Set where
  eq ne lt ge gt le : {{IsIntegral a}} → Comparator [ a ]
  icmpge icmpgt icmpeq icmpne icmplt icmple : Comparator (int ∷ [ int ])

{- Instructions -}
module _ (𝑭 : FrameTy) where

  open import Data.List.Membership.Propositional

  𝑹[_] : Ty → Set
  𝑹[ a ] = a ∈ 𝑭

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
    bop   : NativeBinOp a b c → ε[ ⟨ b ∷ a ∷ ψ  ↝  c ∷ ψ ⟩ ]

    -- register manipulation
    load  : 𝑹[ a ] → ε[ ⟨ ψ ↝ a ∷ ψ ⟩ ]
    store : 𝑹[ a ] → ε[ ⟨ a ∷ ψ ↝ ψ ⟩ ]

    -- jumps
    goto  : ∀[ One ψ₁ ⇒ ⟨ ψ₁ ↝ ψ₂ ⟩ ]
    if    : ∀ {as} → Comparator as → ∀[ One ψ ⇒ ⟨ as ++ ψ ↝ ψ ⟩ ]

  ⟨_∣_↝_⟩ = ⟨_↝_⟩
  Instr = ⟨_↝_⟩

  open import JVM.Syntax.Bytecode StackTy ⟨_↝_⟩ as BC
  open BC using (Code) public

  ⟪_∣_↜_⟫   = ⟪_↜_⟫
  ⟪_∣_↝_⟫   = ⟪_↝_⟫
  ⟪_∣_↝_⟫+  = ⟪_↝_⟫+

module _ {𝑭} where
  open import JVM.Syntax.Bytecode StackTy ⟨ 𝑭 ∣_↝_⟩
    hiding (⟪_↜_⟫; ⟪_↝_⟫; ⟪_↝_⟫+; Code) public
