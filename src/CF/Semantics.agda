module CF.Semantics where

open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.State
open import Relation.Ternary.Monad.Delay
open import Relation.Ternary.Construct.Market

open import JVM.Types
open import JVM.Defaults.Syntax.Values

open import CF.Syntax

eval : ∀ {i} → Expr a Γ → ∀[ Env Γ ⇒ StateT (Delay i) {!!} (Val a) ]
eval = {!!}
