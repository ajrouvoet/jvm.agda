{- MJ where variable declarations have been hoisted to the top of a block -}
module CF.Transform.Hoist where

open import Level
open import Function using (_∘_)
open import Data.List
open import Data.Unit
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Separation
open import Relation.Ternary.Monad
open import Relation.Ternary.Respect.Propositional
open import Relation.Ternary.Monad.Possibly

open import JVM.Types
open import CF.Syntax as Src hiding (Stmt; Block)

module Tgt where
  mutual
    Stmt  = Src.Statements.Statement Block

    {- This is Bigstar, but Agda cannot termination check that -}
    data Block (r : Ty) : Pred Ctx 0ℓ where
      nil  : ε[ Block r ]
      cons : ∀[ Stmt r ✴ Block r ⇒ Block r ]

  -- make constructors visible
  open Src.Statements Block public

open Tgt

pattern _⍮⟨_⟩_ s σ b = cons (s ×⟨ σ ⟩ b)

hoist-binder : ∀ {P : Pred Ctx 0ℓ} {Γ} → ∀[ (Γ Src.⊢ P) ⇒ ◇ (Exactly Γ ✴ P) ]
hoist-binder px = pack (⊢-zip ∙-copy (binders ×⟨ ∙-idˡ ⟩ px))

-- A typed hoisting transformation for statement blocks
{-# TERMINATING #-}
mutual



  {- Hoist local variables from blocks -}
  hoist : ∀[ Src.Block r ⇒ ◇ (Block r) ]
  hoist Src.emp = do
    return nil

  hoist (ss Src.⍮⟨ σ ⟩ b) = do
    b ×⟨ σ ⟩ s               ← translate ss                   &⟨ Src.Block _ # ∙-comm σ ⟩ b
    s ×⟨ σ ⟩ b               ← hoist b                        &⟨ Tgt.Stmt _ # ∙-comm σ ⟩ s
    return (s ⍮⟨ σ ⟩ b)

  hoist (e Src.≔⟨ σ ⟩ Γ⊢b) = do
    e×v ×⟨ σ ⟩ b             ← ⊙-assocₗ ⟨$⟩ (hoist-binder Γ⊢b &⟨ Src.Exp _ # σ ⟩ e)
    (e ×⟨ σ₁ ⟩ v) ×⟨ σ₂ ⟩ b' ← hoist b                        &⟨ _ ✴ _ # σ ⟩ e×v
    return (Tgt.asgn (v ×⟨ ∙-comm σ₁ ⟩ e) ⍮⟨ σ₂ ⟩ b')



  {- Hoist local variables from statements -}
  translate : ∀[ Src.Stmt r ⇒ ◇ (Stmt r) ]

  translate (Src.asgn x) = do
    return (Tgt.asgn x)

  translate (Src.set v×x) = do
    return (Tgt.set v×x)

  translate (Src.run e) = do
    return (Tgt.run e)

  translate (Src.ret e) = do
    return (Tgt.ret e)

  translate (Src.while (e ×⟨ σ ⟩ body)) = do
    e ×⟨ σ ⟩ body'           ← translate body                 &⟨ Src.Exp _ # σ ⟩ e
    return (Tgt.while (e ×⟨ σ ⟩ body'))

  translate (Src.ifthenelse e×s₁×s₂) = do
    let (s₁ ×⟨ σ ⟩ s₂×e) = ⊙-rotateₗ e×s₁×s₂
    s₂ ×⟨ σ ⟩ e×s₁           ← ⊙-assocᵣ ⟨$⟩ (translate s₁     &⟨ _ ✴ _ # ∙-comm σ ⟩ s₂×e)
    e×s₁×s₂                  ← ⊙-assocᵣ ⟨$⟩ (translate s₂     &⟨ _ ✴ _ # ∙-comm σ ⟩ e×s₁)
    return (Tgt.ifthenelse e×s₁×s₂)

  translate (Src.block bl) = do
    bl'                      ← hoist bl
    return (Tgt.block bl')




module Example where

  ex : ◇ (Statement int) ε
  ex = translate (
    Src.ifthenelse (
      num 42
      ×⟨ ∙-idˡ ⟩
      -- then
      Src.run (num 41)
      ×⟨ ∙-idˡ ⟩
      Src.run (num 21)
    ))
  
  binder : ([ int ] Src.⊢ (Src.Block int)) ε
  binder = Possibly.possibly ∼-none Src.emp

  test-binder : ◇ (Exactly [ int ] ✴ Src.Block int) ε
  test-binder = hoist-binder binder

  ex₀ : ◇ (Block int) ε
  ex₀ = hoist (num 42 ≔⟨ ∙-idˡ ⟩ binder)

  ex₂ :  ◇ (Block int) ε
  ex₂ = hoist (Src.run (num 42) ⍮⟨ ∙-idˡ ⟩ Src.run (num 21) ⍮⟨ ∙-idʳ ⟩ Src.emp )
  
  ex₁ : ◇ (Block int) ε
  ex₁ = hoist ( 
    -- int j = 42
    Src.num 42 ≔⟨ ∙-idˡ ⟩ Possibly.possibly ∼-all (
      Src.ifthenelse
        (var refl
          ×⟨ overlaps ∙-idˡ ⟩
          -- then
          Src.block (
            -- int i = j
            var refl ≔⟨ consˡ ∙-idˡ ⟩
            Possibly.possibly ∼-all (
              Src.ret (var refl) Src.⍮⟨ ∙-idʳ ⟩
              emp))
          -- else
          ×⟨ overlaps [] ⟩
          Src.block (
            -- int i = j
            var refl ≔⟨ consˡ ∙-idˡ ⟩
            Possibly.possibly ∼-all (
              Src.ret (var refl) Src.⍮⟨ ∙-idʳ ⟩
              emp))
          )
        Src.⍮⟨ ∙-idʳ ⟩ emp
    ))
