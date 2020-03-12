{-# OPTIONS --safe #-}
module CF.Syntax where

open import Level
open import JVM.Prelude hiding (Σ; _⊢_; _⊆_)

open import Data.List hiding (null)
open import Data.List.Relation.Unary.All
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.PropositionalEquality using (isEquivalence)
open import Relation.Ternary.Separation
open import Relation.Ternary.Monad.Possibly

open import JVM.Types
open import JVM.Contexts

open import Relation.Ternary.Monad.Intros Ty public
open import Relation.Ternary.Data.Allstar Ty

data Exp : Ty → Pred Ctx 0ℓ where
  -- irreducible expressions
  unit     : ε[ Exp void ]
  null     : ε[ Exp (ref a) ]
  num      : ℕ → ε[ Exp int ]

  -- storeless expressions
  var      : ∀[ Just a ⇒ Exp a ]
  iop      : NativeBinOp → ∀[ Exp int ✴ Exp int ⇒ Exp int ]

  -- storeful
  ref   : ∀[ Exp a ⇒ Exp (ref a) ]
  deref : ∀[ Exp (ref a) ⇒ Exp a ]

module Statements (Block : Ty → Pred Ctx 0ℓ) where

  data Statement (r : Ty) : Pred Ctx 0ℓ where
    asgn          : ∀[ Just a ✴ Exp a ⇒ Statement r ]

    set           : ∀[ Exp (ref a) ✴ Exp a ⇒ Statement r ]

    run           : ∀[ Exp a ⇒ Statement r ]
    ret           : ∀[ Exp r ⇒ Statement r ]

    -- ints as bools (false => eq 0, true => ne 0)
    ifthenelse    : ∀[ Exp int ✴ Statement r ✴ Statement r ⇒ Statement r ]
    while         : ∀[ Exp int ✴ Statement r ⇒ Statement r ]
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
pattern _⍮⟨_⟩_ s σ b = cons (s ×⟨ σ ⟩ b)
pattern _≔⟨_⟩_ e σ b = local (e ×⟨ σ ⟩ b)
