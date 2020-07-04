{-# OPTIONS --rewriting #-}
module JVM.Defaults.Syntax.Extrinsic where

open import Agda.Builtin.Equality.Rewrite

open import Data.List as List
open import Data.List.Properties
open import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.Product hiding (swap)

open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Data.Bigstar
open import Relation.Ternary.Data.ReflexiveTransitive as Star
open import Relation.Ternary.Data.IndexedMonoid
open import Relation.Ternary.Construct.Bag.Properties

open import JVM.Types
open import JVM.Defaults.Syntax.Values
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Labeling StackTy
open import JVM.Model.Properties
open import JVM.Defaults.Syntax.Instructions hiding (⟨_↝_⟩; Instr)

{-# REWRITE ++-assoc #-}

Typing = List StackTy

variable
  J₁ J₂ J : Typing

module _ Γ where

  data Instr (J : Typing) : StackTy → StackTy → Set where
    goto  : ψ₁ ∈ J → Instr J ψ₁ ψ₂
    if    : ∀ {as} → Comparator as → ψ₁ ∈ J → Instr J (as ++ ψ₁) ψ₂

    nop   : Instr J ψ₁ ψ₁
    push  : Const a → Instr J ψ₁ (a ∷ ψ₁)
    pop   : Instr J (a ∷ ψ₁) ψ₁
    dup   : Instr J (a ∷ ψ₁) (a ∷ a ∷ ψ₁)
    swap  : Instr J (a ∷ b ∷ ψ₁) (b ∷ a ∷ ψ₁)
    bop   : NativeBinOp a b c → Instr J (a ∷ b ∷ ψ₁) (c ∷ ψ₁)
    load  : a ∈ Γ → Instr J ψ₁ (a ∷ ψ₁)
    store : a ∈ Γ → Instr J (a ∷ ψ₁) ψ₁
    ret   : Instr J (a ∷ ψ₁) ψ₂

  data Bytecode' (J : Typing) : Typing → StackTy → StackTy → Set where
    nil  : Bytecode' J [] ψ₁ ψ₁
    cons : ∀ {I} → Instr J ψ₁ ψ₂ → Bytecode' J I ψ₂ ψ₃ → Bytecode' J (ψ₁ ∷ I) ψ₁ ψ₃
    
  Bytecode : Typing → StackTy → StackTy → Set
  Bytecode J = Bytecode' J J

module _ where

  Addressing : Labels → Typing → Set
  Addressing lbs J = All (λ ψ → ψ ∈ J) lbs
  
  instr-tf : ∀ {Γ ℓs} → Addressing ℓs J → ⟨ Γ ∣ ψ₁ ↝ ψ₂ ⟩ ℓs → Instr (proj₂ Γ) J ψ₁ ψ₂
  instr-tf ρ noop              = nop
  instr-tf ρ pop               = pop
  instr-tf ρ (push x)          = push x
  instr-tf ρ dup               = dup
  instr-tf ρ swap              = swap
  instr-tf ρ (bop x)           = bop x
  instr-tf ρ (load x)          = load x
  instr-tf ρ (store x)         = store x
  instr-tf ρ ret               = ret
  instr-tf (ℓ ∷ _) (goto refl) = goto ℓ
  instr-tf (ℓ ∷ _) (if x refl) = if x ℓ

  Extractor : ∀ Γ → StackTy → StackTy → Intf → Set
  Extractor Γ ψ₁ ψ₂ Φ = {J₁ : Typing} → Addressing (down Φ) J₁ 
                       → ∃ λ J₂ → Bytecode' Γ (J₁ ++ J₂) J₂ ψ₁ ψ₂ × Addressing (up Φ) (J₁ ++ J₂)

  label-addresses : ∀ {x} → Labeling ψ₁ x → All (λ z → z ∈ J₁ ++ ψ₁ ∷ []) x
  label-addresses emp = []
  label-addresses (cons (refl ∙⟨ sep ⟩ qx)) = joinAll (λ ()) sep (∈-++⁺ʳ _ (here refl) ∷ []) (label-addresses qx)

  -- We can extract bytecode that does absolute addressing from the fancy
  -- intrinsically-typed representation.
  -- We do this in a single recursive pass over the bytecode, collecting a global map of instruction typings,
  -- and also collecting indices into that map for every defined label on the forward pass, and 
  -- eliminating labels on the backwards pass.
  --
  -- The interface compositions guide the way. The key lemma is `sinkᵣ`
  -- which says that in order to know what l imports in l ✴ r,
  -- it is sufficient to know what l ✴ r imports, *and* what r exports.
  --
  -- In this setting 'l' is the head of some suffix of bytecode.
  -- The imports of 'l ✴ r' have been collected from the labels defined in the prefix.
  -- We get the exports of the tail 'r' of the suffix from the recursive call.
  extract : ∀ {Γ} → ∀[ ⟪ Γ ∣ ψ₁ ↝ ψ₂ ⟫ ⇒ Extractor (proj₂ Γ) ψ₁ ψ₂ ]
  extract {ψ₁ = ψ₁} nil ρ    = [] , nil , []

  extract {ψ₁ = ψ₁} (cons (labeled (↑ ls ∙⟨ σ₁ ⟩ ↓ i) ∙⟨ σ₂ ⟩ is)) ρ = let
      -- addressing from ↑ ls
      ρ₀ = label-addresses ls
      
      -- Addresses for the labels
      ρ₁ = source σ₁ ρ₀ []
      
      -- Compute addresses for the tail,
      -- by combining the addresses from the state with the addresses for the labels.
      -- We don't need everything, only what is imported in the head instruction.
      ρ₂ = sinkᵣ  σ₂ ρ₁ (All.map (∈-++⁺ˡ {ys = List.[ ψ₁ ]}) ρ)

      -- Recursively extract first to get addressing for forward jumps.
      -- These addresses are exported by the tail.
      k , code , ρ′ = extract is ρ₂

      -- Compute the addresses imported by i
      ρ₃ = sinkᵣ (∙-comm σ₂) ρ′ (All.map ∈-++⁺ˡ ρ)
      ρ₄ = sinkᵣ σ₁ (All.map ∈-++⁺ˡ ρ₀) ρ₃
      
      -- Compute the exported addresses
      ρ₅ = source σ₂ (All.map ∈-++⁺ˡ ρ₁) ρ′

    in ψ₁ ∷ k , cons (instr-tf ρ₄ i) code , ρ₅

  -- Same as above, but simpler
  extract {ψ₁ = ψ₁} (cons (instr   (↓ i) ∙⟨ σ ⟩ b)) ρ =  let
      ρ₂ = sinkᵣ σ [] (All.map (∈-++⁺ˡ {ys = List.[ ψ₁ ]}) ρ)
      k , code , ρ′ = extract b ρ₂
      ρ₃ = sinkᵣ (∙-comm σ) ρ′ (All.map ∈-++⁺ˡ ρ) 
      ρ₄ = source σ [] ρ′
    in ψ₁ ∷ k , cons (instr-tf ρ₃ i) code , ρ₄

-- module Bytecode where

--   open import Data.String as S hiding (show)
  
--   showFin : Fin n → String
--   showFin f = NS.show (Fin.toℕ f)
  
--   showInstr : Instr ℓ → String
--   showInstr (goto x) = "goto " S.++ showFin x
--   showInstr (if x)   = "if " S.++ showFin x 
--   showInstr noop     = "noop"
--   showInstr push     = "push"
--   showInstr pop      = "pop"
--   showInstr dup      = "dup"
--   showInstr swap     = "swap"
--   showInstr bop      = "bop"
--   showInstr load     = "load"
--   showInstr store    = "store"
--   showInstr ret      = "ret"

--   show : Bytecode ℓ n → String
--   show [] = ""
--   show (i ∷ b) = showInstr i S.++ "\n" S.++ show b
