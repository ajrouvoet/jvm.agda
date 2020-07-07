{-# OPTIONS --no-qualified-instances --rewriting #-}
module CF.Transform.UnCo where

open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional

open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad hiding (unit)
open import Relation.Ternary.Monad.Weakening
open import Relation.Ternary.Data.Bigstar hiding ([_])

open import CF.Types
open import CF.Syntax.Hoisted as Hoisted
open import CF.Contexts.Lexical
open import CF.Transform.Hoist
open import CF.Syntax.DeBruijn as Tgt
open Hoisted

open import Relation.Ternary.Data.Allstar Ty

{-# TERMINATING #-}
mutual
  uncoₑ : ∀[ Hoisted.Exp a ⇑ ⇒ Tgt.Exp a ]
  uncoₑ (unit ⇈ wk)     = unit
  uncoₑ (num x ⇈ wk)    = num x
  uncoₑ (bool x ⇈ wk)   = bool x
  uncoₑ (Exp.var' vars ⇈ wk)  = Tgt.var' (member wk)
  uncoₑ (bop f e₁✴e₂ ⇈ wk) with e₁ , e₂ ← unstar (e₁✴e₂ ⇈ wk) = bop f (uncoₑ e₁) (uncoₑ e₂)

  uncos : ∀[ (Allstar Hoisted.Exp as) ⇑ ⇒ Exps as ]
  uncos (nil       ⇈ wk) = []
  uncos (cons e✴es ⇈ wk) with e , es ← unstar (e✴es ⇈ wk) = uncoₑ e ∷ uncos es

{-# TERMINATING #-}
mutual
  uncoₛ : ∀[ Hoisted.Stmt r ⇑ ⇒ Tgt.Stmt r ]
  uncoₛ (run x ⇈ wk) = run (uncoₑ (x ⇈ wk))
  uncoₛ (asgn v✴e ⇈ wk) with unstar (v✴e ⇈ wk)
  ... | vars ⇈ wk' , e⇑ = asgn (member wk') (uncoₑ e⇑)
  uncoₛ (ifthenelse c✴s₁✴s₂ ⇈ wk) = let
    c  , s₁✴s₂ = unstar (c✴s₁✴s₂ ⇈ wk)
    s₁ , s₂    = unstar s₁✴s₂
    in ifthenelse (uncoₑ c) (uncoₛ s₁) (uncoₛ s₂)
  uncoₛ (while c✴s ⇈ wk) with c , s ← unstar (c✴s ⇈ wk) = while (uncoₑ c) (uncoₛ s)
  uncoₛ (block x ⇈ wk) = block (unco' (x ⇈ wk))

  unco' : ∀[ Hoisted.Block r ⇑ ⇒ Tgt.Block r ]
  unco' (nil ⇈ wk) = nil
  unco' (cons s✴b ⇈ wk) with s , b ← unstar (s✴b ⇈ wk) = uncoₛ s ⍮⍮ unco' b

unco : ∀[ Hoisted.Block r ⇒ Tgt.Block r ]
unco bl = unco' (return bl)
