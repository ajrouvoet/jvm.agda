{-# OPTIONS --safe --no-qualified-instances #-}
module CF.Transform.Compile.Expressions where

open import Function using (_∘_)
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

  module Tgt where
    open import JVM.Types public
    open import JVM.Model StackTy public
    open import JVM.Syntax.Values public
    open import JVM.Syntax.Instructions public

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
  compileₑ e₁
  compileₑ e₂
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
      ↓ lfalse⁻ ∙⟨ σ ⟩ lfalse⁺ ← ✴-swap ⟨$⟩ freshLabel 
      lfalse⁺                  ← ✴-id⁻ˡ ⟨$⟩ (code (if cmp lfalse⁻) ⟨ Up _  # σ ⟩& lfalse⁺)
      lfalse⁺                  ← ✴-id⁻ˡ ⟨$⟩ (code (push (bool false)) ⟨ Up _  # ∙-idˡ ⟩& lfalse⁺)
      ↓ lend⁻ ∙⟨ σ ⟩ labels    ← (✴-rotateₗ ∘ ✴-assocᵣ) ⟨$⟩ (freshLabel ⟨ Up _  # ∙-idˡ ⟩& lfalse⁺)
      lfalse⁺ ∙⟨ σ ⟩ lend⁺     ← ✴-id⁻ˡ ⟨$⟩ (code (goto lend⁻) ⟨ _ ✴ _ # σ ⟩& labels)
      lend⁺                    ← ✴-id⁻ˡ ⟨$⟩ (attach lfalse⁺ ⟨ Up _ # σ ⟩& lend⁺)
      code (push (bool true))
      attach lend⁺

    -- Compile comparisons and other binary operations
    compile-bop : ∀ {Γ a b c} → BinOp a b c → ε[ Compiler Γ (⟦ b ⟧ ∷ ⟦ a ⟧ ∷ ψ) (⟦ c ⟧ ∷ ψ) Emp ]
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

compileₑ (ifthenelse c e₁ e₂) = do
  -- condition
  compileₑ c
  lthen+ ∙⟨ σ ⟩ ↓ lthen-  ← freshLabel
  lthen+                  ← ✴-id⁻ˡ ⟨$⟩ (code (if ne lthen-) ⟨ Up _  # ∙-comm σ     ⟩& lthen+)

  -- else
  compileₑ e₂
  ↓ lend- ∙⟨ σ ⟩ labels   ← (✴-rotateₗ ∘ ✴-assocᵣ) ⟨$⟩ (freshLabel ⟨ Up _  # ∙-idˡ        ⟩& lthen+)

  -- then
  lthen+ ∙⟨ σ ⟩ lend+     ← ✴-id⁻ˡ ⟨$⟩ (code (goto lend-) ⟨ _ ✴ _ # σ ⟩& labels)
  lend+                   ← ✴-id⁻ˡ ⟨$⟩ (attach lthen+ ⟨ Up _  # σ ⟩& lend+)
  compileₑ e₁

  -- label the end
  attach lend+

compileₑₛ [] = return refl
compileₑₛ (e ∷ es) = do
  compileₑₛ es
  compileₑ e
