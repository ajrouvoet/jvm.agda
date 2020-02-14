import MJ.Classtable.Core as Core

module CoMJ.Syntax {c}(Ct : Core.Classtable c) where

open import MJ.Prelude
open import Level
open import Data.List hiding (null)
open import Data.List.Relation.Unary.All
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Allstar
open import Relation.Ternary.Separation.Decoration
open import Relation.Unary
open import Data.String

import Data.Vec.All as Vec∀

open import MJ.Classtable.Membership Ct
open import MJ.LexicalScope c
open import MJ.Types c
open Core c
open Classtable Ct

NativeBinOp = ℕ → ℕ → ℕ

data Expr : Ty → Pred ModedCtx 0ℓ where
  -- irreducible expressions
  unit     : ε[ Expr void ]
  null     : ε[ Expr (ref cid) ]
  num      : ℕ → ε[ Expr int ]

  -- storeless expressions
  var      : ∀[ (_≡ ([ a ] , rw ∷ [])) ⇒ Expr a ]
  iop      : NativeBinOp → ∀[ Expr int ✴ Expr int ⇒ Expr int ]
  upcast   : Σ ⊢ cid <: pid → ∀[ Expr (ref cid) ⇒ Expr (ref pid) ]

  -- storeful
  new      : ∀ cid → ∀[ Allstar Expr (constrOf cid)  ⇒ Expr (ref cid) ]
  call     : ∀ {as} {b} m {acc : AccMember cid METHOD m (as , b)} →
             ∀[ Expr (ref cid) ✴ Allstar Expr as ⇒ Expr b ]
  get      : ∀ f {ty}{acc : AccMember cid FIELD f ty} →
             ∀[ Expr (ref cid) ⇒ Expr ty ]

module Statements (Block : Ty → Pred Ctx 0ℓ) where

--   data Statement (r : Ty) : Pred Ctx 0ℓ where
--     asgn          : ∀[ Just a ✴ Expr a ⇒ Statement r ]
--     set           : ∀ {a} f {acc : AccMember cid FIELD f a}
--                     → ∀[ Expr (ref cid) ✴ Expr a ⇒ Statement r ]
--     run           : ∀[ Expr a ⇒ Statement r ]
--     ret           : ∀[ Expr r ⇒ Statement r ]
--     raise         : ε[ Statement r ]
--     trycatch      : ∀[ Statement r ✴ Statement r ⇒ Statement r ]
--     while         : ∀[ Expr int ✴ Statement r ⇒ Statement r ]
--     block         : ∀[ Block r ⇒ Statement r ]
--     ifthenelse    : ∀[ Expr int ✴ Statement r ✴ Statement r ⇒ Statement r ]


-- mutual
--   Stmt = Statements.Statement Block

--   data Block (r : Ty) : Pred Ctx 0ℓ where
--     local : ∀[ Expr a ✴ [ a ] ∣~ (Block r) ⇒ Block r ]
--     cons  : ∀[ Stmt r ✴ Block r ⇒ Block r ]
--     emp   : ε[ Block r ]

-- -- make constructors visible
-- open Statements Block public hiding (Statement)

-- infixr 5 _⍮⟨_⟩_
-- pattern _⍮⟨_⟩_ s σ b = cons (s ×⟨ σ ⟩ b)
