import MJ.Classtable.Core as Core

module JVM.Defaults.Syntax.Exp {c}(Ct : Core.Classtable c) where

open import Level
open import JVM.Prelude hiding (Σ)
open import Data.List hiding (null)
open import Data.List.Relation.Unary.All
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Relation.Ternary.Separation
open import Relation.Unary

import Data.Vec.All as Vec∀

open Core c
open Classtable Ct

open import MJ.Classtable.Membership Ct
open import MJ.Types c
open import JVM.Defaults.Syntax.Frames Ct
open import Relation.Ternary.Data.Allstar Ty

NativeBinOp = ℕ → ℕ → ℕ

Ctx = List Ty

variable
  Γ₁ Γ₂ Γ₃ Γ₄ Γ : Ctx

-- Co-de-bruijn style binders, allowing you to not bring them into scope at all.
-- Once they are in scope of P, they must be used somewhere.
-- This is McBride's (⊢) from EGTBS
record _∣~_ {ℓ} (Γ₁ : Ctx) (P : Pred Ctx ℓ) (Γ₂ : Ctx ) : Set ℓ where
  constructor binder
  field
    bound : (Exactly Γ₁ ✴ (_++ Γ₂) ⊢ P) Γ₁

infixl 10 λ⟨_⟩_
pattern λ⟨_⟩_ σ px = binder (refl ×⟨ σ ⟩ px) 

module _ {p q} {P : Pred Ctx p} {Q : Pred Ctx q} where

  ∣~-map : ∀[ P ⇒ Q ] → ∀[ Γ ∣~ P ⇒ Γ ∣~ Q ]
  ∣~-map f (λ⟨ σ ⟩ px) = λ⟨ σ ⟩ f px

data Expr : Ty → Pred Ctx 0ℓ where
  -- irreducible expressions
  unit     : ε[ Expr void ]
  null     : ε[ Expr (ref cid) ]
  num      : ℕ → ε[ Expr int ]

  -- storeless expressions
  var      : ∀[ Just a ⇒ Expr a ]
  iop      : NativeBinOp → ∀[ Expr int ✴ Expr int ⇒ Expr int ]
  upcast   : Σ ⊢ cid <: pid → ∀[ Expr (ref cid) ⇒ Expr (ref pid) ]

  -- storeful
  new      : ∀ cid → ∀[ Allstar Expr (constrOf cid)  ⇒ Expr (ref cid) ]
  call     : ∀ {as} {b} m {acc : AccMember cid METHOD m (as , b)} →
             ∀[ Expr (ref cid) ✴ Allstar Expr as ⇒ Expr b ]
  get      : ∀ f {ty}{acc : AccMember cid FIELD f ty} →
             ∀[ Expr (ref cid) ⇒ Expr ty ]

module Statements (Block : Ty → Pred Ctx 0ℓ) where

  data Statement (r : Ty) : Pred Ctx 0ℓ where
    asgn          : ∀[ Just a ✴ Expr a ⇒ Statement r ]
    set           : ∀ {a} f {acc : AccMember cid FIELD f a}
                    → ∀[ Expr (ref cid) ✴ Expr a ⇒ Statement r ]
    run           : ∀[ Expr a ⇒ Statement r ]
    ret           : ∀[ Expr r ⇒ Statement r ]
    raise         : ε[ Statement r ]
    trycatch      : ∀[ Statement r ✴ Statement r ⇒ Statement r ]
    while         : ∀[ Expr int ✴ Statement r ⇒ Statement r ]
    block         : ∀[ Block r ⇒ Statement r ]
    ifthenelse    : ∀[ Expr int ✴ Statement r ✴ Statement r ⇒ Statement r ]

mutual
  Stmt = Statements.Statement Block

  data Block (r : Ty) : Pred Ctx 0ℓ where
    local : ∀[ Expr a ✴ [ a ] ∣~ (Block r) ⇒ Block r ]
    cons  : ∀[ Stmt r ✴ Block r ⇒ Block r ]
    emp   : ε[ Block r ]

-- make constructors visible
open Statements Block public hiding (Statement)

infixr 5 _⍮⟨_⟩_
pattern _⍮⟨_⟩_ s σ b = cons (s ×⟨ σ ⟩ b)
