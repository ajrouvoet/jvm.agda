{-# OPTIONS --safe --no-qualified-instances #-}
module CF.Syntax where

open import Level

open import Data.Nat
open import Data.Bool
open import Data.String
open import Data.Product
open import Data.List hiding (null)
open import Data.List.Relation.Unary.All

open import Relation.Unary hiding (_⊢_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.PropositionalEquality using (isEquivalence; refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad.Possibly
open import Relation.Ternary.Monad.Weakening
open import Relation.Ternary.Data.Bigstar hiding ([_])

open import CF.Types
open import CF.Contexts.Lexical

open import Relation.Ternary.Construct.Product using (fst; snd)

open import Relation.Ternary.Data.Allstar Ty

data BinOp : Ty → Ty → Ty → Set where
  add sub mul div xor : BinOp int int int
  eq ne lt ge gt le   : BinOp int int bool

data Exp : Ty → Pred Ctx 0ℓ where
  -- irreducible expressions
  unit     : ε[ Exp void ]
  num      : ℕ → ε[ Exp int ]
  bool     : Bool → ε[ Exp bool ]

  -- storeless expressions
  var'     : ∀[ Var a ⇒ Exp a ]
  bop      : BinOp a b c → ∀[ Exp a ✴ Exp b ⇒ Exp c ]

pattern var  = var' vars

module Statements (Block : Ty → Pred Ctx 0ℓ) where

  data Statement (r : Ty) : Pred Ctx 0ℓ where
    asgn          : ∀[ Var a ✴ Exp a ⇒ Statement r ]
    run           : ∀[ Exp a ⇒ Statement r ]
    ifthenelse    : ∀[ Exp bool ✴ Statement r ✴ Statement r ⇒ Statement r ]
    while         : ∀[ Exp bool ✴ Statement r ⇒ Statement r ]
    block         : ∀[ Block r ⇒ Statement r ]

mutual
  Stmt = Statements.Statement Block

  data Block (r : Ty) : Pred Ctx 0ℓ where
    local : ∀[ Exp a ✴ [ a ] ⊢ (Block r) ⇒ Block r ]
    cons  : ∀[ Stmt r ✴ Block r ⇒ Block r ]
    emp   : ε[ Block r ]

-- make constructors visible
open Statements Block public

infixr 5 _⍮⟨_⟩_
pattern _⍮⟨_⟩_ s σ b = cons (s ∙⟨ σ ⟩ b)
pattern _≔⟨_⟩_ e σ b = local (e ∙⟨ σ ⟩ b)
