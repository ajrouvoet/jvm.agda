{-# OPTIONS --no-qualified-instances #-}
module CF.Transform.UnCo where

open import Data.Product
open import Data.List
open import Data.List.Extra
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional

open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Weakening

open import CF.Types
open import CF.Contexts
open import CF.Transform.Hoist as Src hiding (module Tgt)
open import CF.Syntax.DeBruijn as Tgt

module _ {T : Set} where
  open import Relation.Ternary.Construct.List.Overlapping T using (member) public

open import Relation.Ternary.Data.Allstar Ty

{-# TERMINATING #-}
uncoₑ : ∀[ Src.Exp a ⇑ ⇒ Tgt.Exp a ]
uncoₑ (unit ⇈ wk)     = unit
uncoₑ (num x ⇈ wk)    = num x
uncoₑ (bool x ⇈ wk)   = bool x
uncoₑ (Src.var ⇈ wk)  = Tgt.var (member (proj₂ wk))
uncoₑ (bop f e₁✴e₂ ⇈ wk) with e₁ , e₂ ← unstar (e₁✴e₂ ⇈ wk) = bop f (uncoₑ e₁) (uncoₑ e₂)
uncoₑ (call f✴es ⇈ wk) with unstar (f✴es ⇈ wk)
... | fn ⇈ wk' , es = call (lemma (proj₁ wk')) (uncos es)
  where
    open Overlap
    open import Data.List.Relation.Binary.Permutation.Propositional.Properties

    lemma : ∀ {x : TopLevelDecl} {xs ys} → [ x ] ∙ xs ≣ ys → x ∈ ys
    lemma (hustle ρx _ ρys σ) rewrite ↭-one ρx = let m = member σ in Any-resp-↭ ρys m

    uncos : ∀[ (Allstar Src.Exp as) ⇑ ⇒ Exps as ]
    uncos (nil       ⇈ wk) = []
    uncos (cons e✴es ⇈ wk) with e , es ← unstar (e✴es ⇈ wk) = uncoₑ e ∷ uncos es

{-# TERMINATING #-}
mutual
  uncoₛ : ∀[ Src.Stmt r ⇑ ⇒ Tgt.Stmt r ]
  uncoₛ (run x ⇈ wk) = run (uncoₑ (x ⇈ wk))
  uncoₛ (ret x ⇈ wk) = ret (uncoₑ (x ⇈ wk))
  uncoₛ (asgn v✴e ⇈ wk) with unstar (v✴e ⇈ wk)
  ... | vars ⇈ wk' , e⇑ = asgn (member (proj₂ wk')) (uncoₑ e⇑)
  uncoₛ (ifthenelse c✴s₁✴s₂ ⇈ wk) = let
    c  , s₁✴s₂ = unstar (c✴s₁✴s₂ ⇈ wk)
    s₁ , s₂    = unstar s₁✴s₂
    in ifthenelse (uncoₑ c) (uncoₛ s₁) (uncoₛ s₂)
  uncoₛ (while c✴s ⇈ wk) with c , s ← unstar (c✴s ⇈ wk) = while (uncoₑ c) (uncoₛ s)
  uncoₛ (block x ⇈ wk) = block (unco' (x ⇈ wk))

  unco' : ∀[ Src.Block r ⇑ ⇒ Tgt.Block r ]
  unco' (nil ⇈ wk) = nil
  unco' (cons s✴b ⇈ wk) with s , b ← unstar (s✴b ⇈ wk) = uncoₛ s ⍮⍮ unco' b

unco : ∀[ Src.Block r ⇒ Tgt.Block r ]
unco bl = unco' (return bl)
