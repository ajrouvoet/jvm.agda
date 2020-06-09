{-# OPTIONS --no-qualified-instances #-}
module JVM.Defaults.Printer.Printer {t} (T : Set t) where

open import Function using (_$_; _∘_)
open import Data.Unit
open import Data.Nat
open import Data.Nat.Show as Nat
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.All
open import Relation.Unary hiding (Empty)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

open import JVM.Model T
open import Relation.Ternary.Data.Bigstar
open import Relation.Ternary.Construct.Market intf-rel
open import Relation.Ternary.Monad.Identity as Id hiding (id-monad; id-functor)
open import Relation.Ternary.Monad.State intf-rel

open import JVM.Defaults.Syntax.Labeling T public
open import JVM.Defaults.Printer.Jasmin

Names : List T → Set _
Names = All (λ _ → ℕ)

LabelNames : Pred Intf _
LabelNames (u ⇅ d) = Names u × Names d

PState : Pred Intf _
PState = (λ _ → ℕ × List Stat) ∩ LabelNames

counter : ∀ {Φ} → PState Φ → ℕ
counter = proj₁ ∘ proj₁

Printer : Pt Intf _
Printer = StateT Id PState

open StateTransformer Id {{Id.id-strong}} {PState} public
open import Relation.Ternary.Construct.Bag.Properties
open import Level

module Envs where

  open import Category.Monad
  open import Category.Monad.State as S

  Fresh : Set t → Set _
  Fresh = S.State (Lift t ℕ)
 
  open RawMonadState (StateMonadState (Lift t ℕ)) public

  open import Relation.Ternary.Construct.List duplicate as L
  open import Data.List.Relation.Binary.Permutation.Propositional
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties

  fresh : Fresh (Lift _ ℕ)
  fresh (lift n) = let n' = ℕ.suc n in lift n , lift n'

  freshNames : ∀ xs → Fresh (Names xs)
  freshNames [] = return []
  freshNames (x ∷ xs) = do
    lift n ← fresh
    ns     ← freshNames xs
    return (n ∷ ns)

  env-split-list : ∀ {xs ys zs} → Names xs → L.Split xs ys zs → Fresh (Names ys × Names zs)
  env-split-list nxs []        = return ([] , [])
  env-split-list nxs (consʳ σ) = do
    lift n    ← fresh
    nys , nzs ← env-split-list nxs σ
    return (n ∷ nys , n ∷ nzs)
  env-split-list (nx ∷ nxs) (divide x σ) = do
    nys , nzs ← env-split-list nxs σ
    return (nx ∷ nys , nx ∷ nzs)
  env-split-list (nx ∷ nxs) (consˡ σ) = do
    nys , nzs ← env-split-list nxs σ
    return (nys , nx ∷ nzs)

  env-split-bag : ∀ {xs ys zs} → Names xs → Overlap.BagSplit xs ys zs → Fresh (Names ys × Names zs)
  env-split-bag nxs (Overlap.hustle ρx ρy ρz σ) = do
    let nxs'    = All-resp-↭ (↭-sym ρx) nxs
    (nys , nzs) ← env-split-list nxs' σ
    return (All-resp-↭ ρy nys , All-resp-↭ ρz nzs)

  splitEnv : ∀ {xs ys zs} → xs ∙ ys ≣ zs → LabelNames zs → Fresh (LabelNames xs × LabelNames ys)
  splitEnv (ex (sub {e = e} x x₁) (sub {e = e'} x₄ x₅) σ↑ σ↓) (unv , dnv) = do
      let nu₁' , nu₂' = splitAll (λ ()) σ↑ unv
      let nd₁' , nd₂' = splitAll (λ dup px → px , px ) σ↓ dnv
      nse  , nu₂   ← env-split-bag nu₂' x₁
      nse' , nu₁   ← env-split-bag nu₁' x₅
      let nd₁     = joinAll (λ ()) x  nd₂' nse
      let nd₂     = joinAll (λ ()) x₄ nd₁' nse'
      return ((nu₁ , nd₁) , (nu₂ , nd₂))

module _ where
  open import Relation.Ternary.Monad

  lookUp : ∀ {τ} → ∀[ Up (One τ) ⇒ Printer (Empty ℕ) ]
  lookUp (↑ u) ⟨ supplyᵣ σ ⟩ lift ((n , st) , env) with Envs.splitEnv σ env (lift n)
  ... | ((lab ∷ [] , []) , env₂) , lift n' = lift (emp lab) ∙⟨ ∙-idˡ ⟩ lift ((n' , st) , env₂)

  lookDown : ∀ {τ} → ∀[ Down (One τ) ⇒ Printer (Empty ℕ) ]
  lookDown (↓ u) ⟨ supplyᵣ σ ⟩ lift ((n , st) , env) with Envs.splitEnv σ env (lift n)
  ... | (([] , lab ∷ []) , env₂) , lift n' = lift (emp lab) ∙⟨ ∙-idˡ ⟩ lift ((n' , st) , env₂)

  print : Stat → ε[ Printer Emp ]
  print s ⟨ σ ⟩ lift ((n , st) , env) = lift refl ∙⟨ σ ⟩ lift ((n , s ∷ st) , env)

  print-label : ∀ {τ}  → ∀[ Up (One τ) ⇒ Printer Emp ]
  print-label l = do
    emp n  ← lookUp l
    print (label (Nat.show n))

  {-# TERMINATING #-}
  print-labels : ∀ {τ} → ∀[ Up (Labeling τ) ⇒ Printer Emp ]
  print-labels (↑ emp)                  = return refl
  print-labels (↑ (cons (x ∙⟨ σ ⟩ xs))) = do
    xs ← ✴-id⁻ʳ ⟨$⟩ (print-label (↑ x) &⟨ Up (Labeling _) # ∙-comm $ liftUp σ ⟩ ↑ xs)
    print-labels xs
    where open Disjoint using (bags; bags-isMonoid)

execPrinter : ∀ {P Φ} → Printer P Φ → List Stat
execPrinter pr with pr ⟨ supplyᵣ ∙-idʳ ⟩ proj₁ (initState (lift 0))
  where
    open Envs

    initState : ∀ {Φ} → Envs.Fresh (● PState (supply Φ))
    initState {Φ↑ ⇅ Φ↓} = do
      ns↑ ← freshNames Φ↑
      ns↓ ← freshNames Φ↓
      lift n ← get
      return (lift ((n , []) , (ns↑ , ns↓)))

... | (lift px ∙⟨ σ ⟩ lift ((_ , st) , _)) = reverse st
    
