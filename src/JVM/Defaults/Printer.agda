{-# OPTIONS --no-qualified-instances #-}
module JVM.Defaults.Printer where

open import Function
open import Data.Bool
open import Data.List as List
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Show as Nat
open import Data.Fin
open import Data.String
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax using (Emp; emp)

open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Monad

open import JVM.Types
open import JVM.Contexts using (indexOf)
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions as I
open import JVM.Defaults.Printer.Printer StackTy
open import JVM.Defaults.Printer.Jasmin as J hiding (procedure)

const-instr : Const a → Instr
const-instr Const.null   = aconst_null
const-instr unit         = aconst_null
const-instr (num x)      = sipush x
const-instr (bool false) = iconst0
const-instr (bool true)  = iconst1

load-instr : Ty → ℕ → Instr
load-instr void    = aload
load-instr (ref _) = aload
load-instr int     = iload
load-instr bool    = iload

store-instr : Ty → ℕ → Instr
store-instr void    = astore
store-instr (ref _) = astore
store-instr int     = istore
store-instr bool    = istore

bop-instr : NativeBinOp a b c → Instr
bop-instr add = iadd
bop-instr sub = isub
bop-instr mul = imul
bop-instr div = idiv
bop-instr xor = ixor

if-instr : ∀ {as} → I.Comparator as → String → Instr
if-instr eq = if eq 
if-instr ne = if ne
if-instr lt = if lt
if-instr ge = if ge
if-instr gt = if gt
if-instr le = if le
if-instr icmpge = if icmpge
if-instr icmpgt = if icmpgt
if-instr icmpeq = if icmpeq
if-instr icmpne = if icmpne
if-instr icmplt = if icmplt
if-instr icmple = if icmple

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

  prettyᵢ (↓ (load {a = a} r))  = do
    print (instr (load-instr a (toℕ $ index r)))
  prettyᵢ (↓ (store {a = a} r)) = do
    print (instr (store-instr a (toℕ $ index r)))

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
