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

module Src where
  open import CF.Syntax.DeBruijn as Src hiding (_⍮_) public
  open import CF.Types public
  open import CF.Contexts using (TopLevelTy; TopLevelDecl; FunTy; _⟶_; Ctx; module DeBruijn) public; open DeBruijn
  open TopLevelTy public
  open FunTy public

module Tgt where
  open import JVM.Types public
  open import JVM.Model StackTy public
  open import JVM.Defaults.Syntax.Values public
  open import JVM.Defaults.Syntax.Instructions public hiding (Labels)

open Src
open Tgt

module _ 𝑭 where
  open import CF.Transform.Compile.Monad StackTy ⟨ 𝑭 ∣_⇒_⟩ noop using (Compiler) public

module _ {𝑭} where
  open import CF.Transform.Compile.Monad StackTy ⟨ 𝑭 ∣_⇒_⟩ noop hiding (Compiler) public

{- A typeclass for converting between type disciplines #-}
module _ where

  record To {l r} (L : Set l) (R : Set r) : Set (l ⊔ r) where
    field
      ⟦_⟧ : L → R

  open To {{...}} public

  instance ⟦⟧-list : ∀ {a} {A B : Set a} {{_ : To A B}} → To (List A) (List B)
  To.⟦_⟧ ⟦⟧-list = L.map ⟦_⟧

  instance ⟦⟧-prod : ∀ {a} {A B C D : Set a} {{_ : To A B}} {{_ : To C D}} → To (A × C) (B × D)
  To.⟦_⟧ ⟦⟧-prod = P.map ⟦_⟧ ⟦_⟧

  instance cfToJvm-ty : To Src.Ty Tgt.Ty
  To.⟦_⟧ cfToJvm-ty = ‵_
    where
      ‵_ : Src.Ty → Tgt.Ty
      ‵ void  = boolean
      ‵ int   = int
      ‵ bool  = boolean

  instance cfToJvm-constant : To TopLevelDecl Constant
  To.⟦ cfToJvm-constant ⟧ (name , fun (as ⟶ r)) = staticfun name ⟦ as ⟧ ⟦ r ⟧

  instance cfToJvm-var : ∀ {ℓ} {A B : Set ℓ} {{_ : To A B}} {a : A} {as} →
                         To (a ∈ as) (⟦ a ⟧ ∈ ⟦ as ⟧)
  To.⟦_⟧ cfToJvm-var = ∈-map⁺ ⟦_⟧

-- Compilation of CF expressions
compileₑₛ : ∀ {as ψ K} → Exps as K → ε[ Compiler ⟦ K ⟧ ψ (⟦ as ⟧ ++ ψ) Emp ]

compileₑ : ∀ {a ψ K} → Exp a K → ε[ Compiler ⟦ K ⟧ ψ (⟦ a ⟧ ∷ ψ) Emp ]

compileₑ (unit) = do
  code (push (bool true))

compileₑ (num x) = do
  code (push (num x))

compileₑ (bool b) = do
  code (push (bool b))

compileₑ (var x) = do
  code (load ⟦ x ⟧)

compileₑ (call f es) = do
  refl ← compileₑₛ es
  code (invokestatic ⟦ f ⟧)

compileₑ (bop f e₁ e₂) = do
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
    compile-comp : ∀ {as} → Comparator as → ε[ Compiler 𝑭 (as ++ ψ) (boolean ∷ ψ) Emp ]
    compile-comp cmp = do
      +l ∙⟨ σ ⟩ ↓ -l    ← mklabel
      +l ∙⟨ σ ⟩ refl    ← code (if cmp -l)                               &⟨ Up _  # σ ⟩ +l
      +l ∙⟨ σ ⟩ refl    ← code (push (bool true))                        &⟨ Up _  # σ ⟩ +l
      ↓ -e ∙⟨ σ ⟩ +l∙+e ← ⊙-rotateᵣ ⟨$⟩ (mklabel                         &⟨ Up _  # σ ⟩ +l)
      +l ∙⟨ σ ⟩ +e      ← ⊙-id⁻ʳ ⟨$⟩ (code (goto -e)                     &⟨ _ ⊙ _ # ∙-comm σ ⟩ +l∙+e)
      +e ∙⟨ σ ⟩ refl    ← attachTo +l ⟨ ∙-idʳ ⟩ code (push (bool false)) &⟨ Up _  # ∙-comm σ ⟩ +e
      coe (∙-id⁻ʳ σ) (attach +e)

    -- Compile comparisons and other binary operations
    compile-bop : ∀ {a b c} → BinOp a b c → ε[ Compiler 𝑭 (⟦ a ⟧ ∷ ⟦ b ⟧ ∷ ψ) (⟦ c ⟧ ∷ ψ) Emp ]
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
  refl ← compileₑₛ es
  compileₑ e
