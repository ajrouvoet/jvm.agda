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

open import Relation.Ternary.Construct.GlobalBinding StackTy

{- The writer structure, for incrementaly output bytecode -}
module _ where

  Compiler : Ctx → StackTy → StackTy → Pt Binding 0ℓ
  Compiler Γ τ₁ τ₂ P = ⟪ Γ ∣ τ₁ ⇐ τ₂ ⟫ ⊙ P

  tell  : ∀[ Down ⟨ Γ ∣ τ₁ ⇒ τ₂ ⟩ ⇒ Compiler Γ τ₁ τ₂ Emp ] 
  tell (↓ i) = (instr i ▹⟨ ∙-idʳ ⟩ nil) ∙⟨ ∙-idʳ ⟩ refl

  postulate label : ∀ {P} → ∀[ Up (Just τ₁) ⇒ Compiler Γ τ₁ τ₂ P ─⊙ Compiler Γ τ₁ τ₂ P ]

  postulate instance compiler-monad : Monad StackTy (Compiler Γ)

  mklabel : ∀ τ → ε[ Compiler Γ τ₁ τ₁ (Up (Just τ) ⊙ Down (Just τ)) ]
  mklabel τ = return (binder τ)

{-# TERMINATING #-}
compileₑ : ∀ {ψ : StackTy} → (Exp a ⇑) Γ → ε[ Compiler Γ ψ (a ∷ ψ) Emp ]

compileₑ (unit     ⇈ wk) = tell (↓ (push unit))
compileₑ (null     ⇈ wk) = tell (↓ (push null))
compileₑ (num x    ⇈ wk) = tell (↓ (push (num x)))

compileₑ (var x    ⇈ wk) = tell (↓ (load (x ⇈ wk)))

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

{-# TERMINATING #-}
mutual
  compile : ∀ {ψ : StackTy} → (Stmt r ⇑) Γ → ε[ Compiler Γ ψ ψ Emp ]

  compile (asgn x∙e ⇈ wk) = do
    let x = (x∙e ⇈ wk) >>= π₁
    let e = (x∙e ⇈ wk) >>= π₂

    refl ← compileₑ e
    tell (↓ (store x))

  compile (set e₁∙e₂ ⇈ wk) = do
    let e₁ = (e₁∙e₂ ⇈ wk) >>= π₁
    let e₂ = (e₁∙e₂ ⇈ wk) >>= π₂

    refl ← compileₑ e₁
    refl ← compileₑ e₂

    tell (↓ write)

  compile (run e ⇈ wk) = do
    refl ← compileₑ (e ⇈ wk)
    tell (↓ pop)

  compile (ret e ⇈ wk) = do
    refl ← compileₑ (e ⇈ wk)
    tell (↓ ret)

  compile (block x ⇈ wk) = do
    compiler (x ⇈ wk)

  compile {ψ = ψ} (while e∙s ⇈ wk) = do
    let e    = (e∙s ⇈ wk) >>= π₁
    let body = (e∙s ⇈ wk) >>= π₂

    -- condition
    +c ∙⟨ σ ⟩ -c       ← mklabel ψ
    -c ∙⟨ σ ⟩ refl     ← label +c ⟨ ∙-idʳ ⟩ tell (↓ noop) &⟨ ∙-comm σ ⟩ -c
    -c ∙⟨ σ ⟩ refl     ← compileₑ e                       &⟨ Down _ # σ ⟩ -c
    ↓ -e  ∙⟨ σ ⟩ -c∙+e ← mapM ⊙-rotateᵣ (mklabel ψ        &⟨ Down _ # σ ⟩ -c)
    -c∙+e ∙⟨ σ ⟩ refl  ← tell (↓ (if eq -e))              &⟨ (Down _) ⊙ (Up _) # ∙-comm σ ⟩ -c∙+e

    -- body
    ↓ -c ∙⟨ σ ⟩ +e     ← mapM  ⊙-id⁻ʳ (compile body       &⟨ (Down _) ⊙ (Up _) # σ ⟩ -c∙+e)
    +e   ∙⟨ σ ⟩ refl   ← tell (↓ (goto -c))               &⟨ ∙-comm σ ⟩ +e

    label +e ⟨ σ ⟩ (tell (↓ noop))

  compile {ψ = ψ} (ifthenelse e∙s₁∙s₂ ⇈ wk) = do

    let e₁⇑  = (e∙s₁∙s₂ ⇈ wk) >>= π₁ 
    let else = (e∙s₁∙s₂ ⇈ wk) >>= π₂ >>= π₁
    let then = (e∙s₁∙s₂ ⇈ wk) >>= π₂ >>= π₂

    -- condition
    refl                          ← compileₑ e₁⇑ 
    +t ∙⟨ σ ⟩ ↓ -t                ← mklabel ψ
    +t ∙⟨ σ ⟩ refl                ← tell (↓ (if ne -t))           &⟨ σ ⟩ +t

    -- else
    +t ∙⟨ σ ⟩ refl                ← compile else                    &⟨ Up _ # σ ⟩ +t
    +t ∙⟨ σ₁ ⟩ (+e  ∙⟨ σ₂ ⟩ ↓ -e) ← mklabel ψ                       &⟨ σ ⟩ +t

    -- then
    let _ , σ₃ , σ₄ = ∙-assocₗ σ₁ σ₂
    (+t ∙⟨ σ ⟩ +e) ∙⟨ σ₂ ⟩ refl   ← tell (↓ (goto -e))              &⟨ (Up _) ⊙ (Up _) # σ₄ ⟩ +t ∙⟨ σ₃ ⟩ +e 
    +e ∙⟨ σ ⟩ refl                ← label +t ⟨ ∙-idʳ ⟩ compile then &⟨ Up _ # coe {{∙-respects-≈}} (∙-id⁻ʳ σ₂) (∙-comm σ)  ⟩ +e

    -- labeled end node
    label +e ⟨ σ ⟩ tell (↓ noop)

  compiler : ∀ {ψ : StackTy} → (Block r ⇑) Γ → ε[ Compiler Γ ψ ψ Emp ]
  compiler = {!!}
