import MJ.Classtable.Core as Core

-- Syntax of MJ where variable declarations have been hoisted to the top of a method body.
module JVM.Syntax.Hoisted {c}(Ct : Core.Classtable c) where

open import Level
open import Data.List
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad.Update

open import MJ.Types c
open import MJ.LexicalScope c
open import MJ.Syntax.Typed Ct as Src using (Expr; module Statements; local)
open import MJ.Classtable.Membership Ct
open Core c
open Classtable Ct

open Monads.Monad ⤇-monad
open Monads using (str; typed-str)

mutual
  Stmt  = Statements.Statement Block

  {- This is Bigstar, but Agda cannot termination check that -}
  data Block (r : Ty) : Pred Ctx 0ℓ where
    emp  : ε[ Block r ]
    cons : ∀[ Stmt r ✴ Block r ⇒ Block r ]

-- make constructors visible
open Statements Block public

pattern _⍮⟨_⟩_ s σ b = cons (s ×⟨ σ ⟩ b)

open import Data.Empty
open import Relation.Nullary
module _ where
  open import Data.List.Properties

  -- TODO Generic lemma about list divisions
  postulate smallerˡ : ∀ {x} xs {ys zs : Ctx} → ¬ (x ∷ xs ++ ys) ⊎ zs ≣ ys

  -- TODO Generic lemma about updates in the list division PRSA
  extendˡ : ∀ {P : Pred Ctx 0ℓ} Γ → ∀[ (Γ ++_) ⊢ P ⇒ ⤇ P ] 
  extendˡ Γ px = local (λ fr → -, -, ⊎-∙ₗ fr , px)

-- optimizing hoisting of binders;
hoist-binder : ∀ {P : Pred Ctx 0ℓ} Γ → ∀[ Γ ∣~ P ⇒ ⤇ P ]

-- nullary binder is no binder
hoist-binder [] (λ⟨ [] ⟩ b) =
  return b

-- If a binder only flows to the left, then it is not used
-- in the block; we optimize it away.
hoist-binder (a ∷ Γ) (λ⟨ consˡ sep ⟩ b) =
  -- The co-de-bruijn typing allows us to do just that:
  hoist-binder Γ (λ⟨ sep ⟩ b)

hoist-binder {P} (a ∷ Γ) (λ⟨ duplicate sep ⟩ b) = do
  z ← hoist-binder {P = (a ∷_) ⊢ P} Γ (λ⟨ sep ⟩ b)
  extendˡ [ a ] z

-- It cannot be that a binder does not flow to the left.
-- TODO custom dependent eliminator for _∣~_?
hoist-binder (a ∷ Γ) (λ⟨ consʳ sep ⟩ b)  = ⊥-elim (smallerˡ [] sep)

-- A typed hoisting transformation for statement blocks
{-# TERMINATING #-}
mutual
  hoist : ∀[ Src.Block r ⇒ ⤇ (Block r) ]

  hoist Src.emp = do
    return emp

  hoist (local a Γ⊢b)  = do
    b ← hoist-binder [ a ] Γ⊢b
    hoist b

  hoist (st Src.⍮⟨ σ₁ ⟩ b) = do
    b'  ×⟨ σ₂ ⟩ st  ← hoist b      &⟨ ⊎-comm σ₁ ⟩ st
    st' ×⟨ σ₃ ⟩ b'  ← translate st &⟨ ⊎-comm σ₂ ⟩ b'
    return (st' ⍮⟨ σ₃ ⟩ b')

  translate : ∀[ Src.Stmt r ⇒ ⤇ (Stmt r) ]

  -- boring ones (no recursive occurences of statement)
  translate (Src.asgn x) = do
    return (asgn x)

  translate (Src.set f {acc} x) = do
    return (set f {acc} x)

  translate (Src.run x) = do
    return (run x)

  translate (Src.ret x) = do
    return (ret x)

  translate (Src.raise) = do
    return raise

  translate (Src.trycatch (t ×⟨ σ ⟩ c)) = do
    t' ×⟨ σ ⟩ c  ← translate t &⟨ σ ⟩ c
    c' ×⟨ σ ⟩ t' ← translate c &⟨ ⊎-comm σ ⟩ t'
    return (trycatch (t' ×⟨ ⊎-comm σ ⟩ c'))

  translate (Src.while (e ×⟨ σ ⟩ body)) = do
    body' ×⟨ σ ⟩ e ← translate body &⟨ ⊎-comm σ ⟩ e
    return (while (e ×⟨ ⊎-comm σ ⟩ body'))

  translate (Src.ifthenelse e×s₁×s₂) = do
    let (s₁ ×⟨ σ ⟩ s₂×e) = ✴-rotateₗ e×s₁×s₂
    s₁'×s₂×e ← translate s₁ &⟨ σ ⟩ s₂×e
    let (s₂ ×⟨ σ ⟩ s₁'×e) = ✴-rotateₗ s₁'×s₂×e
    s₂'×e×s₁' ← translate s₂ &⟨ σ ⟩ s₁'×e
    return (ifthenelse (✴-rotateₗ s₂'×e×s₁'))

  translate (Src.block bl) = do
    bl' ← hoist bl
    return (block bl')

module Example where

  ex₁ : ∃₂ λ Φₗ Φ → Φₗ ⊎ [] ≣ Φ × (Block int) Φₗ
  ex₁ = update (hoist ( 
    local int 
    (λ⟨ duplicate ⊎-idˡ ⟩ ( 
      Src.ifthenelse
        (Src.num 42 ×⟨ ⊎-idˡ ⟩
          -- then
          Src.block (
            -- Int i;
            local int (λ⟨ duplicate ⊎-idˡ ⟩ (
            -- i = j;
            Src.asgn (refl ×⟨ ⊎-comm ⊎-∙ ⟩ Expr.var refl) Src.⍮⟨ duplicate ⊎-idʳ ⟩
            -- return j
            Src.ret (Expr.var refl) Src.⍮⟨ ⊎-idʳ ⟩
            Src.emp))
          )
          ×⟨ duplicate ⊎-idˡ ⟩
          -- else
          Src.block (
            -- Int i;
            local int (λ⟨ duplicate ⊎-idˡ ⟩ (
            -- i = j;
            Src.asgn (refl ×⟨ ⊎-comm ⊎-∙ ⟩ Expr.var refl) Src.⍮⟨ duplicate ⊎-idʳ ⟩
            -- return j
            Src.ret (Expr.var refl) Src.⍮⟨ ⊎-idʳ ⟩
            Src.emp))
          )) Src.⍮⟨ consˡ ⊎-idˡ ⟩
      Src.emp)))) ⊎-idˡ
