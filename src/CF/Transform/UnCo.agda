module CF.Transform.UnCo where

open import Data.Product

open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad.Weakening

open import JVM.Types
open import JVM.Contexts

open import CF.Transform.Hoist as Src hiding (module Tgt)
open import CF.Syntax.DeBruijn as Tgt

{-# TERMINATING #-}
uncoₑ : ∀[ Src.Exp a ⇑ ⇒ Tgt.Exp a ]
uncoₑ (unit ⇈ wk)     = unit
uncoₑ (null ⇈ wk)     = null
uncoₑ (num x ⇈ wk)    = num x
uncoₑ (bool x ⇈ wk)   = bool x
uncoₑ (var refl ⇈ wk) = var (member wk)
uncoₑ (bop f e₁✴e₂ ⇈ wk) with e₁ , e₂ ← unstar (e₁✴e₂ ⇈ wk) = bop f (uncoₑ e₁) (uncoₑ e₂)
uncoₑ (ref e ⇈ wk)    = ref (uncoₑ (e ⇈ wk))
uncoₑ (deref e ⇈ wk)  = deref (uncoₑ (e ⇈ wk))

{-# TERMINATING #-}
mutual
  uncoₛ : ∀[ Src.Stmt r ⇑ ⇒ Tgt.Stmt r ]
  uncoₛ (run x ⇈ wk) = run (uncoₑ (x ⇈ wk))
  uncoₛ (ret x ⇈ wk) = ret (uncoₑ (x ⇈ wk))
  uncoₛ (asgn v✴e ⇈ wk) with unstar (v✴e ⇈ wk)
  ... | refl ⇈ wk' , e⇑ = asgn (member wk') (uncoₑ e⇑)
  uncoₛ (set e₁✴e₂ ⇈ wk) with e₁⇑ , e₂⇑ ← unstar (e₁✴e₂ ⇈ wk) = set (uncoₑ e₁⇑) (uncoₑ e₂⇑)
  uncoₛ (ifthenelse c✴s₁✴s₂ ⇈ wk) = let
    c  , s₁✴s₂ = unstar (c✴s₁✴s₂ ⇈ wk)
    s₁ , s₂    = unstar s₁✴s₂
    in ifthenelse (uncoₑ c) (uncoₛ s₁) (uncoₛ s₂)
  uncoₛ (while c✴s ⇈ wk) with c , s ← unstar (c✴s ⇈ wk) = while (uncoₑ c) (uncoₛ s)
  uncoₛ (block x ⇈ wk) = block (unco (x ⇈ wk))

  unco : ∀[ Src.Block r ⇑ ⇒ Tgt.Block r ]
  unco (nil ⇈ wk) = nil
  unco (cons s✴b ⇈ wk) with s , b ← unstar (s✴b ⇈ wk) = uncoₛ s ⍮ unco b
