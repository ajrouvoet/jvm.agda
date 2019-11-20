import MJ.Classtable.Core as Core

module JVM.Syntax.Bytecode {c}(Ct : Core.Classtable c) where

open import Level
open import Function
open import Data.Bool
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Relation.Unary.All
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Separation

open import MJ.Types c
open import MJ.LexicalScope c
open import JVM.Syntax.Frames Ct
open import Data.List.Membership.Propositional {A = RegTy}

module _ where

  Labels  = List FrameTy

  -- The PRSA for Labels
  open import Relation.Ternary.Separation.Construct.Duplicate as Dup
  open import Relation.Ternary.Separation.Construct.List.Intermuted FrameTy
    (Dup.dup-sep FrameTy) {{Dup.dup-is-sep FrameTy}} public

  InitFlags : ∀ {A : Set} → List A → Set
  InitFlags = All (const Bool)

  InstrTy = (Σ[ τ ∈ LocalsTy ] InitFlags τ) × Labels

  -- the PRSA for InstrTy
  open import Relation.Ternary.Separation.Construct.Product public

  Local : RegTy → Pred InstrTy 0ℓ
  Local a = Π₁ (Just a)

  pattern reg = fst refl

{- Instructions -}
module _ where

  data ⟨_⇒_⟩ : StackTy → StackTy → Pred InstrTy 0ℓ where

    -- stack manipulation
    pop  : ε[ ⟨ a ∷ ψ      ⇒  ψ         ⟩ ]
    push : ε[ ⟨ ψ          ⇒  a ∷ ψ     ⟩ ]
    dup  : ε[ ⟨ a ∷ ψ      ⇒  a ∷ a ∷ ψ ⟩ ]
    swap : ε[ ⟨ a ∷ b ∷ ψ  ⇒  b ∷ a ∷ ψ ⟩ ]

    -- register manipulation
    load  : ∀[ Local (init a) ⇒ ⟨ ψ ⇒ a ∷ ψ ⟩ ]
    store : ∀ {i} → ∀[ Local (a , i) ⇒ ⟨ a ∷ ψ ⇒ ψ ⟩ ]

    -- -- jumps
    -- goto  : ∀[ Just ft      ⇒ ⟨ τ ∣ ψ ⇒ τ ∣ ψ       ⟩ ]
    -- if    : ∀[ Just ft      ⇒ ⟨ τ ∣ int ∷ ψ ⇒ τ ∣ ψ ⟩ ]

-- open import Relation.Ternary.Separation.Construct.Exchange Labels public

-- {- Instruction sequences -}
-- module _ where

--   data Label (ft : FrameTy) : Pred Account 0ℓ where
--     label : Label ft ([ ft ] ↕ ε)

--   -- reflexive transitive closure of ⟨_⇒_⟩, with labels
--   data ⟪_⇒_⟫ : (ft₁ ft₂ : FrameTy) → Pred Account 0ℓ where
--     block : ε[ ⟪ ft ⇒ ft ⟫ ]
--     cons  : ∀[ Label ft₁ ✴ ○ ⟨ ft₁ ⇒ ft₂ ⟩ ✴ ⟪ ft₁ ⇒ ft₂ ⟫ ⇒ ⟪ ft₁ ⇒ ft₃ ⟫ ]

--   postulate seq : ∀[ ⟪ ft₁ ⇒ ft₂ ⟫ ⇒ ⟪ ft₂ ⇒ ft₃ ⟫ ─✴ ⟪ ft₁ ⇒ ft₃ ⟫ ]
