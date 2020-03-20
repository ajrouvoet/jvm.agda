{-# OPTIONS --no-qualified-instances #-}
module JVM.Defaults.Printer where

open import Function
open import Data.Fin
open import Data.List as List
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Show as Nat
open import Data.String
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax using (Emp; emp)

open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Weakening using (_⇈_)

open import JVM.Types
open import JVM.Contexts using (indexOf)
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions
open import JVM.Defaults.Printer.Printer StackTy
open import JVM.Defaults.Printer.Jasmin as J hiding (procedure)

const-instr : Const a → Instr
const-instr Const.null = aconst_null
const-instr unit       = aconst_null
const-instr (num x)    = sipush x

load-instr : Ty → ℕ → Instr
load-instr void    = aload
load-instr (ref _) = aload
load-instr int     = iload

store-instr : Ty → ℕ → Instr
store-instr void    = astore
store-instr (ref _) = astore
store-instr int     = istore

bop-instr : NativeBinOp → Instr
bop-instr add = iadd
bop-instr sub = isub
bop-instr mul = imul
bop-instr div = idiv
bop-instr xor = ixor

if-instr : Comparator → String → Instr
if-instr eq = ifeq 
if-instr ne = ifne
if-instr lt = iflt
if-instr ge = ifge
if-instr gt = ifgt
if-instr le = ifle

module _ {Γ} where

  prettyᵢ : ∀ {ψ₁ ψ₂} → ∀[ Down ⟨ Γ ∣ ψ₁ ⇒ ψ₂ ⟩ ⇒ Printer Emp ]
  prettyᵢ (↓ noop)      = print (instr nop)
  prettyᵢ (↓ pop)       = print (instr pop)
  prettyᵢ (↓ dup)       = print (instr dup)
  prettyᵢ (↓ swap)      = print (instr swap)
  prettyᵢ (↓ ret)       = print (instr ret)

  prettyᵢ (↓ (push x))  = print (instr (const-instr x))
  prettyᵢ (↓ (bop x))   = print (instr (bop-instr x))

  prettyᵢ (↓ new)       = print (instr nop)
  prettyᵢ (↓ read)      = print (instr nop)
  prettyᵢ (↓ write)     = print (instr nop)

  prettyᵢ (↓ (load {a = a} (refl ⇈ wk)))  = do
    print (instr (load-instr a (indexOf wk)))
  prettyᵢ (↓ (store {a = a} (refl ⇈ wk))) = do
    print (instr (store-instr a (indexOf wk)))

  prettyᵢ (↓ (goto x))  = do
    emp n ← lookDown (↓ x)
    print (instr (goto (Nat.show n)))
  prettyᵢ (↓ (if c x)) = do
    emp n ← lookDown (↓ x)
    print (instr (if-instr c (Nat.show n)))

  import JVM.Defaults.Syntax.Bytecode.Printer ⟨ Γ ∣_⇒_⟩ prettyᵢ as Printer

  pretty : ∀ {ψ₁ ψ₂ Φ} → ⟪ Γ ∣ ψ₁ ⇒ ψ₂ ⟫ Φ → List Stat
  pretty bc = execPrinter (Printer.pretty bc)

  procedure : ∀ {ψ₁ ψ₂ Φ} → String → ⟪ Γ ∣ ψ₁ ⇒ ψ₂ ⟫ Φ → Jasmin
  procedure name bc = J.procedure name (List.length Γ) 10 (pretty bc)
