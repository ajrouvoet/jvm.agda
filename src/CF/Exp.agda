module CF.Exp where

open import Level
open import JVM.Prelude hiding (Σ; _⊢_; _⊆_)
open import Data.List hiding (null)
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Binary.Sublist.Propositional
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.PropositionalEquality using (isEquivalence)
open import Relation.Ternary.Separation
open import Relation.Ternary.Monad.Possibly

open import JVM.Types
open import JVM.Defaults.Syntax.Frames
open import Relation.Ternary.Data.Allstar Ty

NativeBinOp = ℕ → ℕ → ℕ

Ctx = List Ty

variable
  Γ₁ Γ₂ Γ₃ Γ₄ Γ : Ctx

-- context extension relation
_⊢_⟨∙⟩_ : Ctx → Ctx → Ctx → Set
Δ ⊢ Γ₁ ⟨∙⟩ Γ₂ = ∃ λ (Δ′ : Ctx) → Δ′ ⊆ Δ × Γ₁ ⊎ Δ ≣ Γ₂

⟨∙⟩-preorder : ∀ {Δ} → IsPreorder _≡_ (Δ ⊢_⟨∙⟩_)
IsPreorder.isEquivalence ⟨∙⟩-preorder = isEquivalence
IsPreorder.reflexive ⟨∙⟩-preorder refl = -, ⊆-refl , {!!}
IsPreorder.trans ⟨∙⟩-preorder = {!!}

_⊢_ : Ctx → Pt Ctx 0ℓ
Δ ⊢ P = Possibly.◇ (Δ ⊢_⟨∙⟩_) P

-- open Possibly.◇-Monad {!!} {!!}

-- -- Co-de-bruijn style binders, allowing you to not bring them into scope at all.
-- -- Once they are in scope of P, they must be used somewhere.
-- -- This is McBride's (⊢) from EGTBS
-- record _∣~_ {ℓ} (Γ : Ctx) (P : Pred Ctx ℓ) (Γ₂ : Ctx) : Set ℓ where
--   constructor λ⟨_%_⟩_
--   field
--     Γ≻       : Ctx
--     thinning : Γ≻ ≤ Γ
--     px       : P (Γ₂ ++ Γ≻)

-- infixl 10 λ⟨_⟩_
-- pattern λ⟨_⟩_ σ px = binder (refl ×⟨ σ ⟩ px) 

data Expr : Ty → Pred Ctx 0ℓ where
  -- irreducible expressions
  unit     : ε[ Expr void ]
  null     : ε[ Expr (ref a) ]
  num      : ℕ → ε[ Expr int ]

  -- storeless expressions
  var      : ∀[ Just a ⇒ Expr a ]
  iop      : NativeBinOp → ∀[ Expr int ✴ Expr int ⇒ Expr int ]

  -- storeful
  -- new      : ∀ cid → ∀[ Allstar Expr (constrOf cid)  ⇒ Expr (ref cid) ]
  -- call     : ∀ {as} {b} m {acc : AccMember cid METHOD m (as , b)} →
  --            ∀[ Expr (ref cid) ✴ Allstar Expr as ⇒ Expr b ]
  -- get      : ∀ f {ty}{acc : AccMember cid FIELD f ty} →
  --            ∀[ Expr (ref cid) ⇒ Expr ty ]

module Statements (Block : Ty → Pred Ctx 0ℓ) where

  data Statement (r : Ty) : Pred Ctx 0ℓ where
    asgn          : ∀[ Just a ✴ Expr a ⇒ Statement r ]
    -- set           : ∀ {a} f {acc : AccMember cid FIELD f a}
    --                 → ∀[ Expr (ref cid) ✴ Expr a ⇒ Statement r ]
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
    local : ∀[ [ a ] ⊢ (Block r) ⇒ Block r ]
    cons  : ∀[ Stmt r ✴ Block r ⇒ Block r ]
    emp   : ε[ Block r ]

-- make constructors visible
open Statements Block public hiding (Statement)

infixr 5 _⍮⟨_⟩_
pattern _⍮⟨_⟩_ s σ b = cons (s ×⟨ σ ⟩ b)
