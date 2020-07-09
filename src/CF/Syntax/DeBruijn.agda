{-# OPTIONS --safe #-}
module CF.Syntax.DeBruijn where

open import Level

open import Data.Bool
open import Data.Product
open import Data.Integer
open import Data.List hiding (null)
open import Data.List.Relation.Unary.All
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary hiding (_⊢_)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.PropositionalEquality using (isEquivalence)

open import CF.Types
open import CF.Contexts.Lexical using (Ctx; module DeBruijn; Closed) public
open import CF.Syntax using (BinOp; module BinOp) public

open DeBruijn public
open BinOp    public

mutual
  data Exp : Ty → Pred Ctx 0ℓ where
    unit       : ∀[ Exp void ]
    num        : ℤ    → ∀[ Exp int ]
    bool       : Bool → ∀[ Exp bool ]
    ifthenelse : ∀[ Exp bool ⇒ Exp a ⇒ Exp a ⇒ Exp a ]
    var'       : ∀[ Var a ⇒ Exp a ]
    bop        : BinOp a b c → ∀[ Exp a ⇒ Exp b ⇒ Exp c ]

  Exps = λ as Γ → All (λ a → Exp a Γ) as

mutual
  data Stmt (r : Ty) : Pred Ctx 0ℓ where
    asgn          : ∀[ Var a ⇒ Exp a ⇒ Stmt r ]

    run           : ∀[ Exp a ⇒ Stmt r ]

    ifthenelse    : ∀[ Exp bool ⇒ Stmt r ⇒ Stmt r ⇒ Stmt r ]
    while         : ∀[ Exp bool ⇒ Stmt r ⇒ Stmt r ]
    block         : ∀[ Block r  ⇒ Stmt r ]

  data Block (r : Ty) : Pred Ctx 0ℓ where
    _⍮⍮_  : ∀[ Stmt r ⇒ Block r ⇒ Block r ]
    nil   : ∀[ Block r ]
