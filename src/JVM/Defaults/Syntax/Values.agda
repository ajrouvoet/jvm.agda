{-# OPTIONS --safe #-}
module JVM.Defaults.Syntax.Values where

open import Level
open import Data.Bool
open import Data.Nat
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

open import JVM.Types

-- data Val : Ty → Pred World 0ℓ where
--   null : ε[ Val (ref a) ]
--   unit : ε[ Val void ]
--   num  : ℕ → ε[ Val int ] 
--   bool : Bool → ε[ Val bool ]
--   ref  : ∀[ Just (ref a) ⇒ Val (ref a) ]

data Const : Ty → Set where
  null : ∀ {c} → Const (ref c)
  num  : ℕ     → Const int
  bool : Bool  → Const boolean

-- constvalue : Const a → ε[ Val a ] 
-- constvalue unit    = unit
-- constvalue null    = null
-- constvalue (num x) = num x
-- constvalue (bool x) = bool x

-- open import Relation.Ternary.Data.Allstar Ty

-- Env : Ctx → Pred World 0ℓ
-- Env Γ = Allstar Val Γ
