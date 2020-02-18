module CF.Compile where

open import Level
open import Data.Unit
open import Data.Product
open import Data.List hiding (null)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Data.ReflexiveTransitive
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Weakening

open import CF.Syntax

open import JVM.Types
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Frames
open import JVM.Defaults.Syntax.Instructions

{- The writer structure, for incrementaly output bytecode -}
module _ where

  Compiler : Ctx → StackTy → StackTy → Pt Binding 0ℓ
  Compiler Γ τ₁ τ₂ P = ⟪ Γ ∣ τ₁ ⇐ τ₂ ⟫ ⊙ P

  postulate tell : ∀[ Down ⟨ Γ ∣ τ₁ ⇒ τ₂ ⟩ ⇒ Compiler Γ τ₁ τ₂ Emp ] 

  postulate instance compiler-monad : Monad StackTy (Compiler Γ)

{-# TERMINATING #-}
compileₑ : ∀ {ψ : StackTy} → (Exp a ⇑) Γ → ε[ Compiler Γ ψ (a ∷ ψ) Emp ]

compileₑ (unit     ⇈ wk) = tell (↓ (push unit))
compileₑ (null     ⇈ wk) = tell (↓ (push null))
compileₑ (num x    ⇈ wk) = tell (↓ (push (num x)))

compileₑ (var refl ⇈ wk) = tell (↓ (load (-, wk)))

compileₑ (iop f e₁∙e₂ ⇈ wk) = do
  refl ← compileₑ (th wk (π₁ e₁∙e₂))
  refl ← compileₑ (th wk (π₂ e₁∙e₂))
  tell (↓ (bop f))

compileₑ (ref e    ⇈ wk) = do
  refl ← compileₑ (e ⇈ wk)
  tell (↓ new)

compileₑ (deref e  ⇈ wk) = do
  refl ← compileₑ (e ⇈ wk)
  tell (↓ read)

-- compileₑ unit       = instr (push unit)    ▹⟨ ∙-idʳ ⟩ nil
-- compileₑ null       = instr (push null)    ▹⟨ ∙-idʳ ⟩ nil
-- compileₑ (num n)    = instr (push (num n)) ▹⟨ ∙-idʳ ⟩ nil

-- compileₑ (var x)    = instr (load {!x!}) ▹⟨ ∙-idʳ ⟩ nil
-- compileₑ (iop bop (e₁ ∙⟨ σ ⟩ e₂)) =
--   {!!}
-- compileₑ ref        = {!!}
-- compileₑ (deref e)  = {!!}
