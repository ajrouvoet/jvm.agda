{-# OPTIONS --rewriting #-}

{- MJ where variable declarations have been hoisted to the top of a block -}
module CF.Transform.Hoist where

open import Level
open import Function using (_∘_)
open import Data.List
open import Data.List.Properties
open import Data.Unit
open import Data.Product
open import Relation.Unary hiding (_⊢_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Weakening
open import Relation.Ternary.Structures.Syntax

open import CF.Types
open import CF.Contexts.Lexical
open import CF.Syntax as Src hiding (Stmt; Block; Statement; var) public
open import CF.Syntax.Hoisted as Hoisted

open import Relation.Ternary.Construct.List.Overlapping Ty
open import Relation.Ternary.Data.Bigstar

pattern _⍮⟨_⟩_ s σ b = cons (s ∙⟨ σ ⟩ b)

hoist-binder : ∀ {P : Pred Ctx 0ℓ} {Γ} → ∀[ (Γ ⊢ P) ⇒ ◇ (Vars Γ ✴ P) ]
hoist-binder px = pack (⊢-zip ∙-copy (binders ∙⟨ ∙-idˡ ⟩ px))

-- A typed hoisting transformation for statement blocks
{-# TERMINATING #-}
mutual
  {- Hoist local variables from blocks -}
  hoist : ∀[ Src.Block r ⇒ ◇ (Block r) ]
  hoist Src.emp = do
    return nil

  hoist (ss Src.⍮⟨ σ ⟩ b) = do
    b ∙⟨ σ ⟩ s               ← translate ss                   &⟨ Src.Block _ # ∙-comm σ ⟩ b
    s ∙⟨ σ ⟩ b               ← hoist b                        &⟨ Hoisted.Stmt _ # ∙-comm σ ⟩ s
    return (s ⍮⟨ σ ⟩ b)

  hoist (e Src.≔⟨ σ ⟩ Γ⊢b) = do
    e×v ∙⟨ σ ⟩ b             ← ✴-assocₗ ⟨$⟩ (hoist-binder Γ⊢b &⟨ Src.Exp _ # σ ⟩ e)
    (e ∙⟨ σ₁ ⟩ v) ∙⟨ σ₂ ⟩ b' ← hoist b                        &⟨ _ ✴ _ # σ ⟩ e×v
    return (Hoisted.asgn (v ∙⟨ ∙-comm σ₁ ⟩ e) ⍮⟨ σ₂ ⟩ b')

  {- Hoist local variables from statements -}
  translate : ∀[ Src.Stmt r ⇒ ◇ (Stmt r) ]

  translate (Src.asgn x) = do
    return (Hoisted.asgn x)

  translate (Src.run e) = do
    return (Hoisted.run e)

  translate (Src.ret e) = do
    return (Hoisted.ret e)

  translate (Src.while (e ∙⟨ σ ⟩ body)) = do
    e ∙⟨ σ ⟩ body'           ← translate body                 &⟨ Src.Exp _ # σ ⟩ e
    return (Hoisted.while (e ∙⟨ σ ⟩ body'))

  translate (Src.ifthenelse e×s₁×s₂) = do
    let (s₁ ∙⟨ σ ⟩ s₂×e) = ✴-rotateₗ e×s₁×s₂
    s₂ ∙⟨ σ ⟩ e×s₁           ← ✴-assocᵣ ⟨$⟩ (translate s₁     &⟨ _ ✴ _ # ∙-comm σ ⟩ s₂×e)
    e×s₁×s₂                  ← ✴-assocᵣ ⟨$⟩ (translate s₂     &⟨ _ ✴ _ # ∙-comm σ ⟩ e×s₁)
    return (Hoisted.ifthenelse e×s₁×s₂)

  translate (Src.block bl) = do
    bl'                      ← hoist bl
    return (Hoisted.block bl')

-- -- Optimizing hoisting
-- -- This will throw away the declarations of locals that are not used in the function.
-- hoist-function : ∀[ Src.Function ⇒ Hoisted.Function ]
-- hoist-function (function sig fd σ (possibly args code))
--   with locals , possibly (intros _ refl) code' ← hoist code
--   = function sig fd σ (possibly args (-, possibly ∼-all code')) 

-- hoist-program : Src.Program → Hoisted.Program 
-- hoist-program (program mn σ funs globals) = program mn σ (⊛-map hoist-function funs) globals
