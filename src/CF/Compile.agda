module CF.Compile where

open import Level
open import Data.Unit
open import Data.Product
open import Data.List hiding (null)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Data.ReflexiveTransitive
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Weakening

open import CF.Syntax

open import JVM.Types
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions


{- The writer structure, for incrementaly output bytecode -}
module _ where

  -- The writer monad
  Compiler : Ctx → StackTy → StackTy → Pt Binding 0ℓ
  Compiler Γ τ₁ τ₂ P = ⟪ Γ ∣ τ₁ ⇐ τ₂ ⟫ ⊙ P

  -- Output a single, unlabeled instruction
  tell  : ∀[ Down ⟨ Γ ∣ τ₁ ⇒ τ₂ ⟩ ⇒ Compiler Γ τ₁ τ₂ Emp ] 
  tell i = (instr i ▹⟨ ∙-idʳ ⟩ nil) ∙⟨ ∙-idʳ ⟩ refl

  -- Label the output of a compiler.
  label-start : ∀ {P} → ∀[ Up (Just τ₁) ⇒ Compiler Γ τ₁ τ₂ P ─⊙ Compiler Γ τ₁ τ₂ P ]

  -- oh no, there is no start
  label-start (↑ refl) ⟨ σ₁ ⟩ (nil ∙⟨ σ₂ ⟩ px) rewrite ∙-id⁻ˡ σ₂ =
    (labeled (↑ _ ∙⟨ ∙-idʳ ⟩ ↓ noop) ▹⟨ ∙-idʳ ⟩ nil) ∙⟨ σ₁ ⟩ px

  -- attach the label to the start
  label-start (↑ refl) ⟨ σ₁ ⟩ (i ▹⟨ σ₂ ⟩ ix ∙⟨ σ₃ ⟩ px) with ∙-assocₗ σ₁ σ₃
  ... | _ , σ₄ , σ₅ with ∙-assocₗ σ₄ σ₂
  ... | _ , σ₆ , σ₇ =
    (label (↑ _) ⟨ σ₆ ⟩ i) ▹⟨ σ₇ ⟩ ix ∙⟨ σ₅ ⟩ px

  postulate instance compiler-monad : Monad StackTy (Compiler Γ)

  -- Magically, we can create labels in pairs of positive and negative occurences,
  -- in a pure manner.
  mklabel : ∀ {τ} → ε[ Compiler Γ τ₁ τ₁ (Up (Just τ) ⊙ Down (Just τ)) ]
  mklabel {τ = τ} = return (binder τ)

{-# TERMINATING #-}
compileₑ : ∀ {ψ : StackTy} → (Exp a ⇑) Γ → ε[ Compiler Γ ψ (a ∷ ψ) Emp ]

compileₑ (unit     ⇈ wk) = do
  tell (↓ (push unit))

compileₑ (null     ⇈ wk) = do
  tell (↓ (push null))

compileₑ (num x    ⇈ wk) = do
  tell (↓ (push (num x)))

compileₑ (var x    ⇈ wk) = do
  tell (↓ (load (x ⇈ wk)))

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

  compile (while e∙s ⇈ wk) = do
    let e    = (e∙s ⇈ wk) >>= π₁
    let body = (e∙s ⇈ wk) >>= π₂

    -- condition
    +c ∙⟨ σ ⟩ -c        ← mklabel
    -c ∙⟨ σ ⟩ refl      ← label-start +c ⟨ ∙-idʳ ⟩ tell (↓ noop) &⟨ ∙-comm σ ⟩ -c
    -c ∙⟨ σ ⟩ refl      ← compileₑ e                       &⟨ Down _ # σ ⟩ -c
    (↓ -e) ∙⟨ σ ⟩ -c∙+e ← mapM ⊙-rotateᵣ (mklabel          &⟨ Down _ # σ ⟩ -c)
    -c∙+e  ∙⟨ σ ⟩ refl  ← tell (↓ (if eq -e))              &⟨ (Down _) ⊙ (Up _) # ∙-comm σ ⟩ -c∙+e

    -- body
    ↓ -c ∙⟨ σ ⟩ +e      ← mapM  ⊙-id⁻ʳ (compile body       &⟨ (Down _) ⊙ (Up _) # σ ⟩ -c∙+e)
    +e   ∙⟨ σ ⟩ refl    ← tell (↓ (goto -c))               &⟨ ∙-comm σ ⟩ +e
    label-start +e ⟨ σ ⟩ (tell (↓ noop))

  compile (ifthenelse e∙s₁∙s₂ ⇈ wk) = do

    let e₁⇑  = (e∙s₁∙s₂ ⇈ wk) >>= π₁ 
    let else = (e∙s₁∙s₂ ⇈ wk) >>= π₂ >>= π₁
    let then = (e∙s₁∙s₂ ⇈ wk) >>= π₂ >>= π₂

    -- condition
    refl                ← compileₑ e₁⇑ 
    +t ∙⟨ σ ⟩ ↓ -t      ← mklabel
    +t ∙⟨ σ ⟩ refl      ← tell (↓ (if ne -t))             &⟨ σ ⟩ +t

    -- else
    +t   ∙⟨ σ ⟩ refl    ← compile else                    &⟨ Up _ # σ ⟩ +t
    ↓ -e ∙⟨ σ ⟩ +t∙+e   ← ⊙-rotateᵣ ⟨$⟩ (mklabel          &⟨ σ ⟩ +t)

    -- then
    +t ∙⟨ σ ⟩ +e        ← mapM ⊙-id⁻ʳ (tell (↓ (goto -e)) &⟨ (Up _) ⊙ (Up _) # ∙-comm σ ⟩ +t∙+e) 
    +e ∙⟨ σ ⟩ refl      ← label-start +t ⟨ ∙-idʳ ⟩ compile then &⟨ Up _ # ∙-comm σ  ⟩ +e

    -- labeled end node
    label-start +e ⟨ σ ⟩ tell (↓ noop)

  compiler : ∀ {ψ : StackTy} → (Block r ⇑) Γ → ε[ Compiler Γ ψ ψ Emp ]
  compiler = {!!}
