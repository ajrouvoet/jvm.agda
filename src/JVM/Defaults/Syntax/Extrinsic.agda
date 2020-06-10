{-# OPTIONS --rewriting #-}
module JVM.Defaults.Syntax.Extrinsic where

open import Agda.Builtin.Equality.Rewrite

open import Data.Nat
import Data.Nat.Show as NS
open import Data.Nat.Properties
open import Data.Fin as Fin using (Fin)
open import Data.Vec
open import Data.List
open import Data.List.Relation.Unary.All as All
open import Data.Product hiding (swap)

open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Data.ReflexiveTransitive as Star
open import Relation.Ternary.Data.IndexedMonoid

open import JVM.Types
open import JVM.Model StackTy
open import JVM.Model.Properties
open import JVM.Defaults.Syntax.Instructions hiding (⟨_↝_⟩)

{-# REWRITE +-suc #-}

private
  variable
    ℓ n m : ℕ

module _ where

  data Instr (ℓ : ℕ) : Set where
    goto  : Fin ℓ → Instr ℓ
    if    : Fin ℓ → Instr ℓ

    noop  : Instr ℓ
    push  : Instr ℓ
    pop   : Instr ℓ
    dup   : Instr ℓ
    swap  : Instr ℓ
    bop   : Instr ℓ
    load  : Instr ℓ
    store : Instr ℓ
    ret   : Instr ℓ

  Bytecode : ℕ → ℕ → Set
  Bytecode ℓ n = Vec (Instr ℓ) n

module Bytecode where

  open import Data.String as S hiding (show)
  
  showFin : Fin n → String
  showFin f = NS.show (Fin.toℕ f)
  
  showInstr : Instr ℓ → String
  showInstr (goto x) = "goto " S.++ showFin x
  showInstr (if x)   = "if " S.++ showFin x 
  showInstr noop     = "noop"
  showInstr push     = "push"
  showInstr pop      = "pop"
  showInstr dup      = "dup"
  showInstr swap     = "swap"
  showInstr bop      = "bop"
  showInstr load     = "load"
  showInstr store    = "store"
  showInstr ret      = "ret"

  show : Bytecode ℓ n → String
  show [] = ""
  show (i ∷ b) = showInstr i S.++ "\n" S.++ show b

module _ where

  Addressing : List StackTy → ℕ → Set
  Addressing lbs ℓ = All (λ _ → Fin ℓ) lbs
  
  erase : ∀ {Γ ℓs} → Addressing ℓs n → ⟨ Γ ∣ ψ₁ ↝ ψ₂ ⟩ ℓs → Instr n
  erase ρ noop      = noop
  erase ρ pop       = pop
  erase ρ (push x)  = push
  erase ρ dup       = dup
  erase ρ swap      = swap
  erase ρ (bop x)   = bop
  erase ρ (load x)  = load
  erase ρ (store x) = store
  erase ρ ret       = ret

  erase (i ∷ []) (goto refl) = goto i
  erase (i ∷ []) (if x refl) = if i

  -- We can extract bytecode that does absolute addressing from the fancy
  -- intrinsically-typed representation.
  -- We do this in a single recursive pass over the bytecode, numbering instructions
  -- and collecting addresses for every defined label on the forward pass, and 
  -- eliminating labels on the backwards pass.
  --
  -- The interface compositions guide the way. The key lemma is `sinkᵣ`
  -- which says that in order to know what l imports in l ✴ r,
  -- it is sufficient to know what l ✴ r imports, *and* what r exports.
  --
  -- In this setting 'l' is the head of some suffix of bytecode.
  -- The imports of 'l ✴ r' have been collected from the labels defined in the prefix.
  -- We get the exports of the tail 'r' of the suffix from the recursive call.
  extract : ∀ {Γ Φ} → ⟪ Γ ∣ ψ₁ ↝ ψ₂ ⟫ Φ → Addressing (down Φ) m 
          → ∃ λ n → Bytecode (m + n) n × Addressing (up Φ) (m + n)

  extract nil                     ρ = 0 , [] , []

  extract {m = m} (instr (↓ i) ▹⟨ σ ⟩ is) ρ = 
    suc k , erase ρ₃ i ∷ code , ρ₄
    where
      ρ₂ = sinkᵣ  σ [] (All.map Fin.inject₁ ρ)

      res  = extract is ρ₂
      k    = proj₁ res
      code = proj₁ (proj₂ res)
      ρ′   = proj₂ (proj₂ res)
      
      ρ₃ = sinkᵣ (∙-comm σ) ρ′ (All.map (Fin.inject+ (suc k)) ρ)
      ρ₄ = source σ [] ρ′

  extract {m = m} (labeled (↑ ls ∙⟨ σ₁ ⟩ ↓ i) ▹⟨ σ₂ ⟩ is) ρ =
    suc k , erase ρ₄ i ∷ code , ρ₅
    where
      -- addressing from ↑ ls
      ρ₀ = universal (λ _ → Fin.fromℕ m) _
      
      -- addressing from labeled _
      ρ₁ = source σ₁ ρ₀ []
      
      -- compute addressing for the tail
      ρ₂ = sinkᵣ  σ₂ ρ₁ (All.map Fin.inject₁ ρ)

      res  = extract is ρ₂
      k    = proj₁ res
      code = proj₁ (proj₂ res)
      ρ′   = proj₂ (proj₂ res)

      -- addressing for i
      ρ₃ = sinkᵣ (∙-comm σ₂) ρ′ (All.map (Fin.inject+ (suc k)) ρ)
      ρ₄ = sinkᵣ σ₁ (All.map (Fin.inject+ k) ρ₀) ρ₃
      
      -- return addressing
      ρ₅ = source σ₂ (All.map (Fin.inject+ k) ρ₁) ρ′
