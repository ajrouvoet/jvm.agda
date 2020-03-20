module CF.Compile.Expressions where

open import Level
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List hiding (null; [_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import CF.Transform.Hoist

open import JVM.Types
open import JVM.Contexts
open import JVM.Model StackTy; open Syntax
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions

module _ where
  open import Relation.Ternary.Monad {{ctx-rel}}
  open import Relation.Ternary.Monad.Weakening {{_}} {{ctx-commutative}} {{ctx-monoid}} public
  open Bind {{ctx-monoid}} {{⇑-monad {0ℓ} }} {{IsPartialSemigroup.⊙-respect-≈ ctx-semigroup}} using () renaming (_>>=_ to _⇑->>=_) public

module _ Γ where
  open import CF.Compile.Monad StackTy ⟨ Γ ∣_⇒_⟩ noop using (Compiler) public

module _ {Γ} where
  open import CF.Compile.Monad StackTy ⟨ Γ ∣_⇒_⟩ noop hiding (Compiler) public


  {-# TERMINATING #-}
  compileₑ : ∀ {ψ : StackTy} → (Exp a ⇑) Γ → ε[ Compiler Γ ψ (a ∷ ψ) Emp ]

  compileₑ (unit ⇈ wk) = do
    code (push unit)

  compileₑ (null ⇈ wk) = do
    code (push null)

  compileₑ (num x ⇈ wk) = do
    code (push (num x))

  compileₑ (bool b ⇈ wk) = do
    code (push (bool b))

  compileₑ (var x ⇈ wk) = do
    code (load (x ⇈ wk))

  compileₑ (bop f e₁∙e₂ ⇈ wk) = do
    let e₁ = (e₁∙e₂  ⇈ wk) ⇑->>= π₁
    let e₂ = (e₁∙e₂  ⇈ wk) ⇑->>= (π₂)

    refl ← compileₑ e₂
    refl ← compileₑ e₁
    compile-bop f

    where

      -- a < b compiles to (assume a and b on stack):
      --
      --     if_icmplt -l
      --     iconst_1
      --     goto -e
      -- +l: iconst_0
      -- +e: nop
      --
      -- Other comparisons go similar
      compile-comp : ∀ {as} → Comparator as → ε[ Compiler Γ (as ++ ψ) (bool ∷ ψ) Emp ]
      compile-comp cmp = do
        +l ∙⟨ σ ⟩ ↓ -l    ← mklabel
        +l ∙⟨ σ ⟩ refl    ← code (if cmp -l)                               &⟨ Up _  # σ ⟩ +l
        +l ∙⟨ σ ⟩ refl    ← code (push (bool true))                        &⟨ Up _  # σ ⟩ +l
        ↓ -e ∙⟨ σ ⟩ +l∙+e ← ⊙-rotateᵣ ⟨$⟩ (mklabel                         &⟨ Up _  # σ ⟩ +l)
        +l ∙⟨ σ ⟩ +e      ← ⊙-id⁻ʳ ⟨$⟩ (code (goto -e)                     &⟨ _ ⊙ _ # ∙-comm σ ⟩ +l∙+e)
        +e ∙⟨ σ ⟩ refl    ← attachTo +l ⟨ ∙-idʳ ⟩ code (push (bool false)) &⟨ Up _  # ∙-comm σ ⟩ +e
        coe (∙-id⁻ʳ σ) (attach +e)

      -- Compile comparisons and other binary operations
      compile-bop : BinOp a b c → ε[ Compiler Γ (a ∷ b ∷ ψ) (c ∷ ψ) Emp ]
      compile-bop add = code (bop add)
      compile-bop sub = code (bop sub)
      compile-bop mul = code (bop mul)
      compile-bop div = code (bop div)
      compile-bop xor = code (bop xor)
      compile-bop eq  = compile-comp icmpeq
      compile-bop ne  = compile-comp icmpne
      compile-bop lt  = compile-comp icmplt
      compile-bop ge  = compile-comp icmpge
      compile-bop gt  = compile-comp icmpgt
      compile-bop le  = compile-comp icmplt

  compileₑ (ref e ⇈ wk) = do
    refl ← compileₑ (e  ⇈ wk)
    code new

  compileₑ (deref e ⇈ wk) = do
    refl ← compileₑ (e ⇈ wk)
    code read
