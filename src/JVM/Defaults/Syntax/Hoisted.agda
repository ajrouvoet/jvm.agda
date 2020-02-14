import MJ.Classtable.Core as Core

-- Syntax of MJ where variable declarations have been hoisted to the top of a method body.
module JVM.Defaults.Syntax.Hoisted {c}(Ct : Core.Classtable c) where

open import Level
open import Data.List
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Separation
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Update
open import Relation.Ternary.Respect.Propositional

open import MJ.Types c
open import JVM.Defaults.Syntax.Exp Ct as Src using (_∣~_; Expr; module Statements; local; λ⟨_⟩_; binder)
open import JVM.Defaults.Syntax.Frames Ct
open import MJ.Classtable.Membership Ct
open Core c
open Classtable Ct

-- open import Relation.Ternary.Construct.Duplicate
-- open import Relation.Ternary.Construct.List.Interdivide
--   Ty _ {{dup-is-sep Ty}} public

Ctx = List Ty

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

  -- TODO Generic lemma about list divisions
  postulate smallerˡ : ∀ {x} xs {ys zs : Ctx} → ¬ (x ∷ xs ++ ys) ⊎ zs ≣ ys

  extendˡ : ∀ {P : Pred Ctx 0ℓ} Γ → ∀[ (Γ ++_) ⊢ P ⇒ ⤇ P ] 
  extendˡ Γ px = local (λ fr → -, -, ∙-∙ᵣ fr , px)

-- -- Optimizing hoisting of binders.
-- -- Removes local variable declarations that are not used.
-- hoist-binder : ∀ {P : Pred Ctx 0ℓ} Γ → ∀[ Γ ∣~ P ⇒ ⤇ (Exactly Γ ✴ P) ]

-- -- nullary binder is no binder
-- hoist-binder [] (λ⟨ [] ⟩ b) =
--   return (refl ×⟨ ∙-idˡ ⟩ b)

-- -- If a binder only flows to the left, then it is not used
-- -- in the block; we optimize it away.
-- hoist-binder {P} (a ∷ Γ) (binder (refl ×⟨ consˡ sep ⟩ p)) = do
--   {!!}
--   -- The co-de-bruijn typing allows us to do just that:
--   -- v ×⟨ σ ⟩ p ← hoist-binder {P = (_++ _) ⊢ _} Γ (binder (refl ×⟨ sep ⟩ p))
--   -- return ({!!} ×⟨ {!∙-∙!} ⟩ p)
--   -- refl ×⟨ σ ⟩ b ← hoist-binder {P = (_++ _) ⊢ P} Γ (λ⟨ sep ⟩ {!b!})
--   -- return (refl ×⟨ {!σ!} ⟩ b)

-- hoist-binder {P} (a ∷ Γ) (λ⟨ dups sep ⟩ b) = do
--   {!!}
--   -- refl ×⟨ σ ⟩ z ← hoist-binder Γ (λ⟨ sep ⟩ b)
--   -- {!!} -- extendˡ [ a ] z

-- -- It cannot be that a binder does not flow to the left.
-- -- TODO custom dependent eliminator for _∣~_?
-- hoist-binder (a ∷ Γ) (λ⟨ consʳ sep ⟩ b)  = ⊥-elim (smallerˡ [] sep)

-- -- A typed hoisting transformation for statement blocks
-- {-# TERMINATING #-}
-- mutual
--   hoist : ∀[ Src.Block r ⇒ ⤇ (Block r) ]

--   hoist Src.emp = do
--     return emp

--   hoist (local (e ×⟨ σ ⟩ Γ⊢b))  = do
--     e×v×b ← hoist-binder [ _ ] Γ⊢b &⟨ Expr _ # σ ⟩ e
--     let (e×v ×⟨ σ ⟩ b) = ⊙-assocₗ e×v×b
--     (e ×⟨ σ₁ ⟩ v) ×⟨ σ₂ ⟩ b' ← hoist b &⟨ _ ✴ _ # σ ⟩ e×v
--     return (asgn (v ×⟨ ∙-comm σ₁ ⟩ e) ⍮⟨ σ₂ ⟩ b')

--   hoist (st Src.⍮⟨ σ₁ ⟩ b) = do
--     st ×⟨ σ₂ ⟩ b'  ← hoist b      &⟨ σ₁ ⟩ st
--     b' ×⟨ σ₃ ⟩ st' ← translate st &⟨ ∙-comm σ₂ ⟩ b'
--     return (st' ⍮⟨ ∙-comm σ₃ ⟩ b')

--   translate : ∀[ Src.Stmt r ⇒ ⤇ (Stmt r) ]

--   -- boring ones (no recursive occurences of statement)
--   translate (Src.asgn x) = do
--     return (asgn x)

--   translate (Src.set f {acc} x) = do
--     return (set f {acc} x)

--   translate (Src.run x) = do
--     return (run x)

--   translate (Src.ret x) = do
--     return (ret x)

--   translate (Src.raise) = do
--     return raise

--   translate (Src.trycatch (t ×⟨ σ ⟩ c)) = do
--     c  ×⟨ σ ⟩ t' ← translate t &⟨ ∙-comm σ ⟩ c
--     t' ×⟨ σ ⟩ c' ← translate c &⟨ {!!} ⟩ t'
--     return (trycatch (t' ×⟨ {!!} ⟩ c'))

--   translate (Src.while (e ×⟨ σ ⟩ body)) = do
--     e ×⟨ σ ⟩ body' ← translate body &⟨ σ ⟩ e
--     return (while (e ×⟨ σ ⟩ body'))

--   translate (Src.ifthenelse e×s₁×s₂) = do
--     {!!}
--     -- let (s₁ ×⟨ σ ⟩ s₂×e) = ⊙-rotateₗ e×s₁×s₂
--     -- s₁'×s₂×e ← translate s₁ &⟨ σ ⟩ s₂×e
--     -- let (s₂ ×⟨ σ ⟩ s₁'×e) = ⊙-rotateₗ s₁'×s₂×e
--     -- s₂'×e×s₁' ← translate s₂ &⟨ σ ⟩ s₁'×e
--     -- return (ifthenelse (⊙-rotateₗ s₂'×e×s₁'))

--   translate (Src.block bl) = do
--     bl' ← hoist bl
--     return (block bl')

-- -- module Example where

-- --   ex₁ : ∃₂ λ Φₗ Φ → Φₗ ⊎ [] ≣ Φ × (Block int) Φₗ
-- --   ex₁ = update (hoist ( 
-- --     local int 
-- --     (λ⟨ duplicate ⊎-idˡ ⟩ ( 
-- --       Src.ifthenelse
-- --         (Src.num 42 ×⟨ ⊎-idˡ ⟩
-- --           -- then
-- --           Src.block (
-- --             -- Int i;
-- --             local int (λ⟨ duplicate ⊎-idˡ ⟩ (
-- --             -- i = j;
-- --             Src.asgn (refl ×⟨ ⊎-comm ⊎-∙ ⟩ Expr.var refl) Src.⍮⟨ duplicate ⊎-idʳ ⟩
-- --             -- return j
-- --             Src.ret (Expr.var refl) Src.⍮⟨ ⊎-idʳ ⟩
-- --             Src.emp))
-- --           )
-- --           ×⟨ duplicate ⊎-idˡ ⟩
-- --           -- else
-- --           Src.block (
-- --             -- Int i;
-- --             local int (λ⟨ duplicate ⊎-idˡ ⟩ (
-- --             -- i = j;
-- --             Src.asgn (refl ×⟨ ⊎-comm ⊎-∙ ⟩ Expr.var refl) Src.⍮⟨ duplicate ⊎-idʳ ⟩
-- --             -- return j
-- --             Src.ret (Expr.var refl) Src.⍮⟨ ⊎-idʳ ⟩
-- --             Src.emp))
-- --           )) Src.⍮⟨ consˡ ⊎-idˡ ⟩
-- --       Src.emp)))) ⊎-idˡ
