{-# OPTIONS --rewriting #-}
module JVM.Transform.Assemble where

open import Agda.Builtin.Equality.Rewrite

open import Data.Nat using (ℕ)
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
open import JVM.Syntax.Values
open import JVM.Model StackTy
open import JVM.Model.Properties
open import JVM.Syntax.Labeling StackTy
open import JVM.Syntax.Instructions hiding (⟨_↝_⟩; Instr)

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
    bop   : NativeBinOp a b c → Instr J (b ∷ a ∷ ψ₁) (c ∷ ψ₁)
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
  
  instr-tf : ∀ {Γ ℓs} → Addressing ℓs J → ⟨ Γ ∣ ψ₁ ↝ ψ₂ ⟩ ℓs → Instr Γ J ψ₁ ψ₂
  instr-tf ρ noop              = nop
  instr-tf ρ pop               = pop
  instr-tf ρ (push x)          = push x
  instr-tf ρ dup               = dup
  instr-tf ρ swap              = swap
  instr-tf ρ (bop x)           = bop x
  instr-tf ρ (load x)          = load x
  instr-tf ρ (store x)         = store x
  instr-tf (ℓ ∷ _) (goto refl) = goto ℓ
  instr-tf (ℓ ∷ _) (if x refl) = if x ℓ

  Extractor : ∀ Γ → StackTy → StackTy → Intf → Set
  Extractor Γ ψ₁ ψ₂ Φ = {J₁ : Typing} → Addressing (down Φ) J₁ 
                       → ∃ λ J₂ → Bytecode' Γ (J₁ ++ J₂) J₂ ψ₁ ψ₂ × Addressing (up Φ) (J₁ ++ J₂)

  exec-extractor : ∀ {Γ} → Extractor Γ ψ₁ ψ₂ ε → ∃ λ J → Bytecode Γ J ψ₁ ψ₂
  exec-extractor c = let _ , code , _ = c {[]} [] in -, code

  label-addresses : ∀ {x} → Labeling ψ₁ x → All (λ z → z ∈ J₁ ++ ψ₁ ∷ []) x
  label-addresses (refl ∙⟨ σ ⟩ qx) = joinAll (λ ()) σ (∈-++⁺ʳ _ (here refl) ∷ []) (addr' qx)
    where
      addr' : ∀ {x} → Bigstar (Own List.[ ψ₁ ]) x → All (λ z → z ∈ J₁ ++ ψ₁ ∷ []) x
      addr' emp = []
      addr' (cons (refl ∙⟨ σ ⟩ qx)) = joinAll (λ ()) σ (∈-++⁺ʳ _ (here refl) ∷ []) (addr' qx)

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
  extract : ∀ {Γ} → ∀[ ⟪ Γ ∣ ψ₁ ↝ ψ₂ ⟫ ⇒ Extractor Γ ψ₁ ψ₂ ]
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

module Show where

  open import Data.String as S hiding (show)
  open import Data.Integer as I
  open import Data.Fin as Fin
  open import Data.Nat.Show as NS
  open import Data.Bool.Show as BS
  
  showInt : ℤ → String
  showInt (+ n) = NS.show n
  showInt (-[1+ n ]) = "-" S.++ NS.show (ℕ.suc n)
  
  showFin : ∀ {n} → Fin n → String
  showFin f = NS.show (Fin.toℕ f)
  
  showComp : Comparator as → String
  showComp eq = "eq"
  showComp ne = "ne"
  showComp lt = "lt"
  showComp ge = "ge"
  showComp gt = "gt"
  showComp le = "le"
  showComp icmpge = "icmpge"
  showComp icmpgt = "icmpgt"
  showComp icmpeq = "icmpeq"
  showComp icmpne = "icmpne"
  showComp icmplt = "icmplt"
  showComp icmple = "icmple"

  showOp : NativeBinOp a b c → String
  showOp add = "add"
  showOp sub = "sub"
  showOp mul = "mul"
  showOp div = "div"
  showOp xor = "xor"

  showConst : Const a → String
  showConst Const.null = "null"
  showConst (num x)    = showInt x
  showConst (bool x)   = BS.show x

  showReg : ∀ {Γ} → a ∈ Γ → String
  showReg e = showFin (index e)
  
  showLabel : ψ ∈ J → String
  showLabel = λ ℓ → showFin (index ℓ)
  
  showInstr : ∀ {Γ} → Instr Γ J ψ₁ ψ₂ → String
  showInstr (goto ℓ) = "goto " S.++ showLabel ℓ
  showInstr (if c ℓ) = "if " S.++ (showComp c S.++ " " S.++ showLabel ℓ)
  showInstr nop      = "noop"
  showInstr (push c) = "push " S.++ (showConst c)
  showInstr pop      = "pop"
  showInstr dup      = "dup"
  showInstr swap     = "swap"
  showInstr (bop o)  = "bop " S.++ (showOp o)
  showInstr (load r) = "load " S.++ (showReg r)
  showInstr (store r)= "store " S.++ (showReg r)
  showInstr ret      = "ret"
  
  showTy : Ty → String
  showTy boolean = "bool"
  showTy byte    = "byte"
  showTy short   = "short"
  showTy int     = "int"
  showTy long    = "long"
  showTy char    = "char"
  showTy (ref x) = "ref"
  showTy (array t) = "array"
  
  showStackTy : StackTy → String
  showStackTy []      = "[]"
  showStackTy (x ∷ ψ) = showTy x S.++ " : " S.++ showStackTy ψ

  showBytecode : ∀ {Γ J} → Bytecode Γ J ψ₁ ψ₂ → String
  showBytecode b = showBytecode' b 0
    where
      open import Data.Nat

      showBytecode' : ∀ {Γ J J'} → Bytecode' Γ J J' ψ₁ ψ₂ → ℕ → String
      showBytecode' nil n = ""
      showBytecode' (cons {ψ₁ = ψ₁} {ψ₂} i b) n = 
        NS.show n S.++ ": " 
          S.++ showInstr i
          S.++ "\t⟨ " S.++ showStackTy ψ₁ S.++ " ↝ " S.++ showStackTy ψ₂ S.++ " ⟩"
          S.++ "\n" S.++ showBytecode' b (ℕ.suc n)
