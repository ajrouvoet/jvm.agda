module CF.Compile where

open import Data.Product
open import Data.List hiding (null; [_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import CF.Transform.Hoist
open import CF.Compile.Expressions

open import JVM.Types
open import JVM.Contexts
open import JVM.Model StackTy; open Syntax
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
    tell (↓ (store x))

  compile (set e₁∙e₂ ⇈ wk) = do
    let e₁ = (e₁∙e₂ ⇈ wk) ⇑->>= π₁
    let e₂ = (e₁∙e₂ ⇈ wk) ⇑->>= π₂

    refl ← compileₑ e₁
    refl ← compileₑ e₂

    tell (↓ write)

  compile (run e ⇈ wk) = do
    refl ← compileₑ (e  ⇈ wk)
    tell (↓ pop)

  compile (ret e ⇈ wk) = do
    refl ← compileₑ (e  ⇈ wk)
    tell (↓ ret)

  compile (block x ⇈ wk) = do
    compiler (x  ⇈ wk)

  compile {ψ = ψ} (while e∙s ⇈ wk) = do
    let e    = (e∙s ⇈ wk) ⇑->>= π₁
    let body = (e∙s ⇈ wk) ⇑->>= π₂

    -- condition
    +c ∙⟨ σ ⟩ -c        ← mklabel {τ = ψ}
    -c ∙⟨ σ ⟩ refl      ← label-start +c ⟨ ∙-idʳ ⟩ tell (↓ noop) &⟨ Down _ # ∙-comm σ ⟩ -c
    -c ∙⟨ σ ⟩ refl      ← compileₑ e                       &⟨ Down _ # σ ⟩ -c
    (↓ -e) ∙⟨ σ ⟩ -c∙+e ← mapM ⊙-rotateᵣ (mklabel          &⟨ Down _ # σ ⟩ -c)
    -c∙+e  ∙⟨ σ ⟩ refl  ← tell (↓ (if eq -e))              &⟨ (Down _) ⊙ (Up _) # ∙-comm σ ⟩ -c∙+e

    -- body
    ↓ -c ∙⟨ σ ⟩ +e      ← ⊙-id⁻ʳ {{⊙-respect-≈}} ⟨$⟩ (compile body &⟨ (Down _) ⊙ (Up _) # σ ⟩ -c∙+e)
    +e   ∙⟨ σ ⟩ refl    ← tell (↓ (goto -c))               &⟨ Up _ # ∙-comm σ ⟩ +e
    label-start +e ⟨ σ ⟩ (tell (↓ noop))

  compile {ψ = ψ} (ifthenelse e∙s₁∙s₂ ⇈ wk) = do
    let e₁   = (e∙s₁∙s₂ ⇈ wk) ⇑->>= π₁ 
    let else = (e∙s₁∙s₂ ⇈ wk) ⇑->>= π₂ ⇑->>= π₁
    let then = (e∙s₁∙s₂ ⇈ wk) ⇑->>= π₂ ⇑->>= π₂

    -- condition
    refl                ← compileₑ e₁
    +t ∙⟨ σ ⟩ ↓ -t      ← mklabel {τ = ψ}
    +t ∙⟨ σ ⟩ refl      ← tell (↓ (if ne -t))             &⟨ Up _ # σ ⟩ +t

    -- else
    +t   ∙⟨ σ ⟩ refl    ← compile else                    &⟨ Up _ # σ ⟩ +t
    ↓ -e ∙⟨ σ ⟩ +t∙+e   ← ⊙-rotateᵣ ⟨$⟩ (mklabel { τ = ψ } &⟨ Up _ # σ ⟩ +t)

    -- then
    +t ∙⟨ σ ⟩ +e        ← ⊙-id⁻ʳ {{ ⊙-respect-≈ }} ⟨$⟩ (tell (↓ (goto -e)) &⟨ _⊙_ (Up _) (Up _) # ∙-comm σ ⟩ +t∙+e)
    +e ∙⟨ σ ⟩ refl      ← label-start +t ⟨ ∙-idʳ ⟩ compile then &⟨ Up _ # ∙-comm σ  ⟩ +e

    -- labeled end node
    label-start +e ⟨ σ ⟩ tell (↓ noop)

  {- Compiling blocks -}
  compiler : ∀ {ψ : StackTy} → (Block r ⇑) Γ → ε[ Compiler Γ ψ ψ Emp ]  

  compiler (nil ⇈ wk) = do
    return refl

  compiler ((cons s∙b) ⇈ wk) = do
    let s = (s∙b ⇈ wk) ⇑->>= π₁
    let b = (s∙b ⇈ wk) ⇑->>= π₂

    refl ← compile s
    compiler b 
