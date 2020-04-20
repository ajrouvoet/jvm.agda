{-# OPTIONS --no-qualified-instances #-}
module CF.Transform.Compile.Statements where

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
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions

mutual
  {- Compiling statements -}
  compileₛ : ∀ {ψ : StackTy} {Γ r} → Stmt r Γ → ε[ Compiler ⟦ Γ ⟧ ψ ψ Emp  ]

  compileₛ (asgn x e) = do
    compileₑ e
    code (store ⟦ x ⟧)

  compileₛ (run e) = do
    compileₑ e 
    code pop

  compileₛ (ret e) = do
    compileₑ e 
    code ret

  compileₛ (block x) = do
    compiler _ x

  -- do while? abstraction -- for loops
  compileₛ (while e body) = do
    -- c⁺: [[ e ]]
    -- iffalse e⁻
    -- [[ body ]]
    -- goto c⁻
    -- e⁺: nop

    -- condition
    c⁺ ∙⟨ σ ⟩ c⁻        ← mklabel
    c⁻ ∙⟨ σ ⟩ refl      ← attachTo c⁺ ⟨ ∙-idʳ ⟩ compileₑ e         &⟨ Down _ # ∙-comm σ ⟩ c⁻
    (↓ e⁻) ∙⟨ σ ⟩ c⁻∙e⁺ ← mapM ✴-rotateᵣ (mklabel                  &⟨ Down _ # σ        ⟩ c⁻)
    c⁻∙e⁺  ∙⟨ σ ⟩ refl  ← code (if eq e⁻)                          &⟨ _ ✴ _  # ∙-comm σ ⟩ c⁻∙e⁺

    -- body
    ↓ c⁻ ∙⟨ σ ⟩ e⁺      ← ✴-id⁻ʳ ⟨$⟩ (compileₛ body                &⟨ _ ✴ _  # σ        ⟩ c⁻∙e⁺)
    e⁺   ∙⟨ σ ⟩ refl    ← code (goto c⁻)                           &⟨ Up _   # ∙-comm σ ⟩ e⁺

    -- label the end
    coe (∙-id⁻ʳ σ) (attach e⁺)

  compileₛ (ifthenelse c then else) = do

    -- condition
    refl                ← compileₑ c
    t⁺ ∙⟨ σ ⟩ ↓ t⁻      ← mklabel
    t⁺ ∙⟨ σ ⟩ refl      ← code (if ne t⁻)                              &⟨ Up _  # σ        ⟩ t⁺

    -- else
    t⁺   ∙⟨ σ ⟩ refl    ← compileₛ else                                &⟨ Up _  # σ        ⟩ t⁺
    ↓ e⁻ ∙⟨ σ ⟩ t⁺∙e⁺   ← ✴-rotateᵣ ⟨$⟩ (mklabel                       &⟨ Up _  # σ        ⟩ t⁺)

    -- then
    t⁺ ∙⟨ σ ⟩ e⁺        ← ✴-id⁻ʳ ⟨$⟩ (code (goto e⁻)                   &⟨ _ ✴ _ # ∙-comm σ ⟩ t⁺∙e⁺)
    e⁺ ∙⟨ σ ⟩ refl      ← attachTo t⁺ ⟨ ∙-idʳ ⟩ compileₛ then          &⟨ Up _  # ∙-comm σ ⟩ e⁺

    -- label the end
    coe (∙-id⁻ʳ σ) (attach e⁺)

  {- Compiling blocks -}
  compiler : ∀ (ψ : StackTy) {Γ r} → Block r Γ → ε[ Compiler ⟦ Γ ⟧ ψ ψ Emp ]  

  compiler ψ (nil) = do
    return refl

  compiler ψ (s ⍮⍮ b) = do
    compileₛ s
    compiler _ b 
