open import Data.List

module JVM.Defaults.Transform.Contextualize.Monad (T : Set) (I : T → T → List T → Set) where

open import Function using (_$_; _∘_)
open import Data.Unit
open import Data.Nat
open import Data.Nat.Show as Nat
open import Data.Product
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional
open import Relation.Unary hiding (Empty; _∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Data.ReflexiveTransitive as Star
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Update
open import Relation.Ternary.Data.IndexedMonoid

open import JVM.Model T using (Intf; _⇅_; up; down)

open import JVM.Defaults.Syntax.Contextual.Interface T
open import JVM.Defaults.Syntax.Contextual.Bytecode T I

open import Relation.Ternary.Construct.Market disjoint-split
open import Relation.Ternary.Monad.State disjoint-split
open import Relation.Ternary.Monad.Writer market-rel

open WriterMonad




-- Names : LabelCtx → LabelCtx → Set _
-- Names I E = All (λ τ → τ ∈ E) I

-- Output : T → T → Market → Set
-- Output τ₁ τ₂ = ○ (Bytecode {!!} τ₁ τ₂)

-- output-monoid : IsIndexedMonoid Output
-- output-monoid = {!!}

-- data Inner (S : Market → Set) : Market → Set where
--   inner : ∀ {m} → Inner S (supply m)

-- Contextualizer : T → T → Intf → Pt LabelCtx _
-- Contextualizer τ₁ τ₂ K = STATET {!!} (Names (down K)) (Names (up K)) -- (Writer output-monoid τ₁ τ₂)

-- Contextualizer : T → T → Intf → Set
-- Contextualizer τ₁ τ₂ K = ∀ {E₁} → Names E₁ (down K) 
--                        → ∃₂ λ E₂ E → (E₁ ∙ E₂ ≣ E) × Bytecode E τ₁ τ₂ E₂ × Names E (up K)


-- end : ∀ {τ} → Contextualizer τ τ ([] ⇅ [])
-- end ns = -, -, ∙-idʳ , nil , []

-- _>>_ : Contextualizer τ₁ τ₂ 
