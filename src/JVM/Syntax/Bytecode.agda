import MJ.Classtable.Core as Core

module JVM.Syntax.Bytecode {c}(Ct : Core.Classtable c) where

open import Level
open import Data.Bool
open import Data.Product hiding (swap)
open import Data.List
open import Relation.Unary hiding (_∈_)
open import Relation.Ternary.Separation

open import MJ.Types c
open import JVM.Syntax.Frames Ct
open import Relation.Ternary.Separation.Construct.Duplicate FrameTy
open import Relation.Ternary.Separation.Construct.List.Intermuted FrameTy dup-sep {{dup-is-sep}}
open import Data.List.Membership.Propositional {A = RegTy}

Labels = List FrameTy

{- Instructions -}
module _ where

  data ⟨_⇒_⟩ : (ft₁ ft₂ : FrameTy) → Labels → Set where

    -- stack manipulation
    pop  : ε[ ⟨ τ ∣ a ∷ ψ     ⇒   τ ∣ ψ         ⟩ ]
    push : ε[ ⟨ τ ∣ ψ         ⇒   τ ∣ a ∷ ψ     ⟩ ]
    dup  : ε[ ⟨ τ ∣ a ∷ ψ     ⇒   τ ∣ a ∷ a ∷ ψ ⟩ ]
    swap : ε[ ⟨ τ ∣ a ∷ b ∷ ψ ⇒   τ ∣ b ∷ a ∷ ψ ⟩ ]

    -- register manipulation
    load  : (init a) ∈ τ              → ε[ ⟨ τ ∣ ψ ⇒ τ ∣ a ∷ ψ ⟩ ]
    store : ∀ {i} → (r : (a , i) ∈ τ) → ε[ ⟨ τ ∣ a ∷ ψ ⇒ r ∷= init a ∣ ψ ⟩ ]

    -- jumps
    goto  : ∀[ Just ft      ⇒ ⟨ τ ∣ ψ ⇒ τ ∣ ψ       ⟩ ]
    if    : ∀[ Just ft      ⇒ ⟨ τ ∣ int ∷ ψ ⇒ τ ∣ ψ ⟩ ]

open import Relation.Ternary.Separation.Construct.Exchange Labels

{- Instruction sequences -}
module _ where

  data Label (ft : FrameTy) : Pred Account 0ℓ where
    labeled : Label ft ([ ft ] ↕ ε)

  -- reflexive transitive closure of ⟨_⇒_⟩
  data ⟪_⇒_⟫ : (ft₁ ft₂ : FrameTy) → Pred Account 0ℓ where

    []   : ε[ ⟪ ft ⇒ ft ⟫ ]
    cons : ε[ Label ft₁ ✴ ○ ⟨ ft₁ ⇒ ft₂ ⟩ ✴ ⟪ ft₂ ⇒ ft₃ ⟫ ⇒ ⟪ ft₁ ⇒ ft₃ ⟫ ]
