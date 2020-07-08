{-# OPTIONS --no-qualified-instances #-}
module CF.Transform.Compile.Statements where

open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.List hiding (null; [_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

open import CF.Syntax.DeBruijn
open import CF.Transform.Compile.Expressions
open import CF.Types
open import CF.Transform.Compile.ToJVM

open import JVM.Types
open import JVM.Compiler
open import JVM.Contexts
open import JVM.Model StackTy
open import JVM.Syntax.Values
open import JVM.Syntax.Instructions

mutual
  {- Compiling statements -}
  compileₛ : ∀ {ψ : StackTy} {Γ r} → Stmt r Γ → ε[ Compiler ⟦ Γ ⟧ ψ ψ Emp  ]

  compileₛ (asgn x e) = do
    compileₑ e
    code (store ⟦ x ⟧)

  compileₛ (run e) = do
    compileₑ e 
    code pop

  compileₛ (block x) = do
    compiler _ x

  compileₛ (while e body) = do
    -- condition
    lcond⁺ ∙⟨ σ ⟩ lcond⁻    ← freshLabel
    refl ∙⟨ σ ⟩ lcond⁻      ← attachTo lcond⁺ ⟨ ∙-idʳ ⟩ compileₑ e ⟨ Down _ # σ ⟩& lcond⁻
    (↓ lend⁻) ∙⟨ σ ⟩ labels ← (✴-rotateₗ ∘ ✴-assocᵣ) ⟨$⟩ (freshLabel ⟨ Down _ # σ ⟩& lcond⁻)
    (↓ lcond⁻) ∙⟨ σ ⟩ lend⁺ ← ✴-id⁻ˡ ⟨$⟩ (code (if eq lend⁻) ⟨ _ ✴ _  # σ ⟩& labels)

    -- body
    compileₛ body
    lend⁺                   ← ✴-id⁻ˡ ⟨$⟩ (code (goto lcond⁻) ⟨ Up _   # σ ⟩& lend⁺)
    attach lend⁺

  compileₛ (ifthenelse c e₁ e₂) = do
    -- condition
    compileₑ c
    lthen+ ∙⟨ σ ⟩ ↓ lthen-  ← freshLabel
    lthen+                  ← ✴-id⁻ˡ ⟨$⟩ (code (if ne lthen-) ⟨ Up _  # ∙-comm σ     ⟩& lthen+)

    -- else
    compileₛ e₂
    ↓ lend- ∙⟨ σ ⟩ labels   ← (✴-rotateₗ ∘ ✴-assocᵣ) ⟨$⟩ (freshLabel ⟨ Up _  # ∙-idˡ        ⟩& lthen+)

    -- then
    lthen+ ∙⟨ σ ⟩ lend+     ← ✴-id⁻ˡ ⟨$⟩ (code (goto lend-) ⟨ _ ✴ _ # σ ⟩& labels)
    lend+                   ← ✴-id⁻ˡ ⟨$⟩ (attach lthen+ ⟨ Up _  # σ ⟩& lend+)
    compileₛ e₁

    -- label the end
    attach lend+
    
  {- Compiling blocks -}
  compiler : ∀ (ψ : StackTy) {Γ r} → Block r Γ → ε[ Compiler ⟦ Γ ⟧ ψ ψ Emp ]  

  compiler ψ (nil) = do
    return refl

  compiler ψ (s ⍮⍮ b) = do
    compileₛ s
    compiler _ b 
