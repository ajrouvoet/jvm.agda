module CF.Syntax where

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

-- context extension relation
_⊢_⟨∙⟩_ : Ctx → Ctx → Ctx → Set
Δ ⊢ Γ₁ ⟨∙⟩ Γ₂ = ∃ λ (Δ′ : Ctx) → Δ′ ⊆ Δ × Γ₁ ⊎ Δ ≣ Γ₂

_⊢_ : Ctx → Pt Ctx 0ℓ
Δ ⊢ P = Possibly.◇ (Δ ⊢_⟨∙⟩_) P

-- ⟨∙⟩-preorder : ∀ {Δ} → IsPreorder _≡_ (Δ ⊢_⟨∙⟩_)
-- IsPreorder.isEquivalence ⟨∙⟩-preorder = isEquivalence
-- IsPreorder.reflexive ⟨∙⟩-preorder refl = -, ⊆-refl , {!!}
-- IsPreorder.trans ⟨∙⟩-preorder = {!!}
-- open Possibly.◇-Monad {!!} {!!}

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
    local : ∀[ [ a ] ⊢ (Block r) ⇒ Block r ]
    cons  : ∀[ Stmt r ✴ Block r ⇒ Block r ]
    emp   : ε[ Block r ]

-- make constructors visible
open Statements Block public hiding (Statement)

infixr 5 _⍮⟨_⟩_
pattern _⍮⟨_⟩_ s σ b = cons (s ×⟨ σ ⟩ b)
