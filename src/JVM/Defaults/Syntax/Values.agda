module JVM.Defaults.Syntax.Values where

open import JVM.Prelude hiding (Σ; _⊢_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import JVM.Types
open import JVM.Defaults.Syntax.Frames

data Val : Ty → Pred World 0ℓ where
  null : ε[ Val (ref a) ]
  unit : ε[ Val void ]
  num  : ℕ → ε[ Val int ] 
  ref  : ∀[ Just (ref a) ⇒ Val (ref a) ]

data Const : Ty → Set where
  null : ∀ {c} → Const (ref c)
  num  : ℕ     → Const int

constvalue : Const a → ε[ Val a ] 
constvalue null    = null
constvalue (num x) = num x
