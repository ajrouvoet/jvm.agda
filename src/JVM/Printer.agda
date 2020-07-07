{-# OPTIONS --no-qualified-instances #-}
module JVM.Defaults.Printer where

open import Function
open import Data.Bool
open import Data.Product hiding (swap)
open import Data.List as L
open import Data.List.Relation.Unary.Any
open import Data.Nat as N
open import Data.Nat.Show as Nat
open import Data.Fin
open import Data.String as S
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax hiding (_∣_)

open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Monad

open import JVM.Types
open import JVM.Contexts using (indexOf)
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions as I
open import JVM.Defaults.Printer.Printer StackTy
open import JVM.Defaults.Printer.Jasmin as J hiding (procedure)

private
  module _ {T : Set} where
    open import JVM.Model T public

const-instr : Const a → Instr
const-instr Const.null   = aconst_null
const-instr (num x)      = sipush x
const-instr (bool false) = iconst0
const-instr (bool true)  = iconst1

load-instr : Ty → ℕ → Instr
load-instr (ref _)   = aload
load-instr (array _) = iload
load-instr int     = iload
load-instr boolean = iload
load-instr byte    = iload
load-instr short   = iload
load-instr long    = iload
load-instr char    = iload

store-instr : Ty → ℕ → Instr
store-instr (ref _)   = astore
store-instr (array _) = aastore
store-instr int     = istore
store-instr boolean = istore
store-instr byte    = istore
store-instr short   = istore
store-instr long    = istore
store-instr char    = istore

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

module _ {𝑭} where

  prettyᵢ : ∀ {ψ₁ ψ₂} → ∀[ Down ⟨ 𝑭 ∣ ψ₁ ↝ ψ₂ ⟩ ⇒ Printer Emp ]
  prettyᵢ (↓ noop)      = print (instr nop)
  prettyᵢ (↓ pop)       = print (instr pop)
  prettyᵢ (↓ dup)       = print (instr dup)
  prettyᵢ (↓ swap)      = print (instr swap)
  prettyᵢ (↓ ret)       = print (instr ret)

  prettyᵢ (↓ (push x))  = print (instr (const-instr x))
  prettyᵢ (↓ (bop x))   = print (instr (bop-instr x))

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

  -- prettyᵢ (↓ (new c))   = print (instr nop)
  -- prettyᵢ (↓ (getstatic s)) = print (instr nop)
  -- prettyᵢ (↓ (getfield  s)) = print (instr nop)
  -- prettyᵢ (↓ (putfield  s)) = print (instr nop)
  -- prettyᵢ (↓ (invokestatic  {𝑐 = 𝑐} {𝑚} {as} {r = r} f))  =
  --   print (instr (invokestatic (𝑐 / 𝑚 :⟨ as ⟩ r))) 
  -- prettyᵢ (↓ (invokevirtual {𝑐 = 𝑐} {𝑚} {as = as} {r} f)) =
  --   print (instr (invokestatic (𝑐 / 𝑚 :⟨ as ⟩ r))) 
  -- prettyᵢ (↓ (invokespecial {𝑐 = 𝑐} {𝑚} {as = as} {r} f)) =
  --   print (instr (invokespecial (𝑐 / 𝑚 :⟨ as ⟩ r))) 

  import JVM.Defaults.Syntax.Bytecode.Printer ⟨ 𝑭 ∣_↝_⟩ prettyᵢ as Printer

  pretty : ∀ {ψ₁ ψ₂ Φ} → ⟪ 𝑭 ∣ ψ₁ ↝ ψ₂ ⟫ Φ → List Stat
  pretty bc = execPrinter (Printer.pretty bc)

  procedure : ∀ {ψ₁ ψ₂ Φ} → String → ⟪ 𝑭 ∣ ψ₁ ↝ ψ₂ ⟫ Φ → Jasmin
  procedure name bc = J.procedure name (L.length (proj₂ 𝑭)) 10 (pretty bc)

-- module _ where

--   open import JVM.Builtins
--   open import JVM.Defaults.Syntax.Classes

--   ofClass : Down⁻ Class jre → Jasmin
--   ofClass (cls , _ ∙⟨ _ ⟩ members) = jasmin
--     (record { class_spec = class cls ; super_spec = super Object })
--     (fieldsOf members)
--     ( defaultInit       -- currently no way to do typed init
--     ∷ methodsOf members
--     )

--      where
--        open import Relation.Ternary.Data.Bigstar
--        open import Data.Maybe

--        access = "public" ∷ "static" ∷ []

--        mth : ∀ {Φ} → Member Φ → Maybe Method
--        mth (virtual   (cls / name :⟨ as ⟩ r) , _ ∙⟨ _ ⟩ ↓ (locs , body)) =
--          just (method name access (L.length locs N.+ L.length as) 50 as r (pretty body))
--        mth (staticfun (cls / name :⟨ as ⟩ r) , _ ∙⟨ _ ⟩ ↓ (locs , body)) =
--          just (method name access (L.length locs N.+ L.length as) 50 as r (pretty body))
--        mth _  = nothing

--        fld : ∀ {Φ} → Member Φ → Maybe ClassField
--        fld (staticref (cls / name ∶ t) , _) = just (clsfield cls access t)
--        fld _ = nothing

--        fieldsOf : ∀ {Φ} → Bigstar Member Φ → List ClassField
--        fieldsOf emp           = []
--        fieldsOf (m ✴⟨ _ ⟩ ms) with fld m
--        ... | just f  = f ∷ fieldsOf ms
--        ... | nothing = fieldsOf ms

--        methodsOf : ∀ {Φ} → Bigstar Member Φ → List Method
--        methodsOf emp           = []
--        methodsOf (m ✴⟨ _ ⟩ ms) with mth m
--        ... | just f  = f ∷ methodsOf ms
--        ... | nothing = methodsOf ms
