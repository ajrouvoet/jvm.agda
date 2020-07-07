{-# OPTIONS --no-qualified-instances #-}
module CF.Transform.Compile.Expressions where

open import Level
open import Data.Unit
open import Data.Bool
open import Data.Product as P
open import Data.List as L hiding (null; [_])
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary hiding (_∈_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Construct.Bag.Properties

private
  module Src where
    open import CF.Syntax.DeBruijn public
    open import CF.Types public
    open import CF.Contexts.Lexical using (module DeBruijn) public; open DeBruijn public
    open FunTy public

  module Tgt where
    open import JVM.Types public
    open import JVM.Model StackTy public
    open import JVM.Defaults.Syntax.Values public
    open import JVM.Defaults.Syntax.Instructions public

open Src
open Tgt

open import JVM.Compiler
open import CF.Transform.Compile.ToJVM

-- Compilation of CF expressions
compileₑₛ : ∀ {as ψ Γ} → Exps as Γ → ε[ Compiler ⟦ Γ ⟧ ψ (⟦ as ⟧ ++ ψ) Emp ]

compileₑ  : ∀ {a ψ Γ}  → Exp a Γ   → ε[ Compiler ⟦ Γ ⟧ ψ (⟦ a ⟧ ∷ ψ) Emp ]

compileₑ (unit) = do
  code (push (bool true))

compileₑ (num x) = do
  code (push (num x))

compileₑ (bool b) = do
  code (push (bool b))

compileₑ (var' x) = do
  code (load ⟦ x ⟧)

compileₑ (bop f e₁ e₂) = do
  compileₑ e₂
  compileₑ e₁
  compile-bop f

  where

    -- a < b compiles to (assume a and b on stack):
    --
    --     if_icmplt l⁻
    --     iconst_1
    --     goto e⁻
    -- l⁺: iconst_0
    -- e⁺: nop
    --
    -- Other comparisons go similar
    compile-comp : ∀ {Γ as} → Comparator as → ε[ Compiler Γ (as ++ ψ) (boolean ∷ ψ) Emp ]
    compile-comp cmp = do
      l⁺ ∙⟨ σ ⟩ ↓ l⁻    ← freshLabel 
      l⁺ ∙⟨ σ ⟩ refl    ← code (if cmp l⁻)                               &⟨ Up _  # σ ⟩ l⁺
      l⁺ ∙⟨ σ ⟩ refl    ← code (push (bool true))                        &⟨ Up _  # σ ⟩ l⁺
      ↓ e⁻ ∙⟨ σ ⟩ l⁺∙e⁺ ← ✴-rotateᵣ ⟨$⟩ (freshLabel                       &⟨ Up _  # σ ⟩ l⁺)
      l⁺ ∙⟨ σ ⟩ e⁺      ← ✴-id⁻ʳ ⟨$⟩ (code (goto e⁻)                     &⟨ _ ✴ _ # ∙-comm σ ⟩ l⁺∙e⁺)
      e⁺                ← ✴-id⁻ʳ ⟨$⟩ (attachTo l⁺ ⟨ ∙-idʳ ⟩ code (push (bool false)) &⟨ Up _  # ∙-comm σ ⟩ e⁺)
      attach e⁺

    -- Compile comparisons and other binary operations
    compile-bop : ∀ {Γ a b c} → BinOp a b c → ε[ Compiler Γ (⟦ a ⟧ ∷ ⟦ b ⟧ ∷ ψ) (⟦ c ⟧ ∷ ψ) Emp ]
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

compileₑₛ [] = return refl
compileₑₛ (e ∷ es) = do
  compileₑₛ es
  compileₑ e
