{-# OPTIONS --no-qualified-instances #-}
module CF.Compile where

open import Data.Product
open import Data.List hiding (null; [_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

open import CF.Transform.Hoist
open import CF.Compile.Expressions

open import JVM.Types
open import JVM.Contexts
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions

{-# TERMINATING #-}
mutual
  {- Compiling statements -}
  compile : ∀ {ψ : StackTy} → (Stmt r ⇑) Γ → ε[ Compiler Γ ψ ψ Emp  ]

  compile (asgn x∙e ⇈ wk) = do
    let x = (x∙e  ⇈ wk) ⇑->>= π₁
    let e = (x∙e  ⇈ wk) ⇑->>= π₂

    refl ← compileₑ e
    code (store x)

  compile (set e₁∙e₂ ⇈ wk) = do
    let e₁ = (e₁∙e₂ ⇈ wk) ⇑->>= π₁
    let e₂ = (e₁∙e₂ ⇈ wk) ⇑->>= π₂

    refl ← compileₑ e₁
    refl ← compileₑ e₂

    code write

  compile (run e ⇈ wk) = do
    refl ← compileₑ (e  ⇈ wk)
    code pop

  compile (ret e ⇈ wk) = do
    refl ← compileₑ (e  ⇈ wk)
    code ret

  compile (block x ⇈ wk) = do
    compiler _ (x  ⇈ wk)

  -- do while? abstraction -- for loops
  compile {ψ = ψ} (while e∙s ⇈ wk) = do
    let e    = (e∙s ⇈ wk) ⇑->>= π₁
    let body = (e∙s ⇈ wk) ⇑->>= π₂

    -- condition
    +c ∙⟨ σ ⟩ -c        ← mklabel {τ = ψ}
    -c ∙⟨ σ ⟩ refl      ← attachTo +c ⟨ ∙-idʳ ⟩ compileₑ e         &⟨ Down _ # ∙-comm σ ⟩ -c
    (↓ -e) ∙⟨ σ ⟩ -c∙+e ← mapM ⊙-rotateᵣ (mklabel                  &⟨ Down _ # σ        ⟩ -c)
    -c∙+e  ∙⟨ σ ⟩ refl  ← code (if eq -e)                          &⟨ _ ⊙ _  # ∙-comm σ ⟩ -c∙+e

    -- body
    ↓ -c ∙⟨ σ ⟩ +e      ← ⊙-id⁻ʳ ⟨$⟩ (compile body &⟨ _ ⊙ _  # σ        ⟩ -c∙+e)
    +e   ∙⟨ σ ⟩ refl    ← code (goto -c)                           &⟨ Up _   # ∙-comm σ ⟩ +e

    -- label the end
    coe (∙-id⁻ʳ σ) (attach +e)

  compile {ψ = ψ} (ifthenelse e∙s₁∙s₂ ⇈ wk) = do
    let e₁   = (e∙s₁∙s₂ ⇈ wk) ⇑->>= π₁ 
    let then = (e∙s₁∙s₂ ⇈ wk) ⇑->>= π₂ ⇑->>= π₁
    let else = (e∙s₁∙s₂ ⇈ wk) ⇑->>= π₂ ⇑->>= π₂

    -- condition
    refl                ← compileₑ e₁
    +t ∙⟨ σ ⟩ ↓ -t      ← mklabel {τ = ψ}
    +t ∙⟨ σ ⟩ refl      ← code (if ne -t)                              &⟨ Up _  # σ        ⟩ +t

    -- else
    +t   ∙⟨ σ ⟩ refl    ← compile else                                 &⟨ Up _  # σ        ⟩ +t
    ↓ -e ∙⟨ σ ⟩ +t∙+e   ← ⊙-rotateᵣ ⟨$⟩ (mklabel { τ = ψ }             &⟨ Up _  # σ        ⟩ +t)

    -- then
    +t ∙⟨ σ ⟩ +e        ← ⊙-id⁻ʳ ⟨$⟩ (code (goto -e) &⟨ _ ⊙ _ # ∙-comm σ ⟩ +t∙+e)
    +e ∙⟨ σ ⟩ refl      ← attachTo +t ⟨ ∙-idʳ ⟩ compile then           &⟨ Up _  # ∙-comm σ ⟩ +e

    -- label the end
    coe (∙-id⁻ʳ σ) (attach +e)

  {- Compiling blocks -}
  compiler : ∀ (ψ : StackTy) → (Block r ⇑) Γ → ε[ Compiler Γ ψ ψ Emp ]  

  compiler ψ (nil ⇈ wk) = do
    return refl

  compiler ψ ((cons s∙b) ⇈ wk) = do
    let s = (s∙b ⇈ wk) ⇑->>= π₁
    let b = (s∙b ⇈ wk) ⇑->>= π₂

    refl ← compile s
    compiler _ b 
