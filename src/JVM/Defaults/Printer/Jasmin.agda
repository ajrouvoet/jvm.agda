module JVM.Defaults.Printer.Jasmin where

open import Function
open import Data.Nat
open import Data.Nat.Show as NatShow
open import Data.String hiding (show)
open import Data.List as List

sep : List (List String) → List String
sep = List.concat ∘ List.intersperse [ "" ]

record ClassSpec : Set where
  constructor class
  field
    class_name : String

  out : List String
  out = ".class" ∷ "public" ∷ class_name ∷ []

record SuperSpec : Set where
  constructor super
  field
    class_name : String

  out : List String
  out = ".super" ∷ class_name ∷ []

record Header : Set where
  field
    class_spec : ClassSpec
    super_spec : SuperSpec

  out : List String
  out = List.concat $
        ClassSpec.out class_spec
      ∷ SuperSpec.out super_spec
      ∷ []

Desc : Set
Desc = List String

data Instr : Set where
  nop pop dup swap ret : Instr

  aconst_null   : Instr
  iconst        : ℕ → Instr

  aload iload   : ℕ → Instr
  astore istore : ℕ → Instr

  new           : String → Instr

  ifeq ifne ifle iflt ifge ifgt goto : String → Instr

  iadd isub imul idiv ixor : Instr
  
module Instruction where

  out : Instr → List String
  out nop         = [ "nop" ]
  out pop         = [ "pop" ]
  out dup         = [ "dup" ]
  out swap        = [ "swap" ]
  out ret         = [ "return" ]
  out aconst_null = [ "aconst_null" ]

  out (iconst n)  = "iconst" ∷ NatShow.show n ∷ []
  out (aload n)   = "aload"  ∷ NatShow.show n ∷ []
  out (iload n)   = "iload"  ∷ NatShow.show n ∷ []
  out (astore n)  = "astore" ∷ NatShow.show n ∷ []
  out (istore n)  = "istore" ∷ NatShow.show n ∷ []

  out (goto l)    = "goto" ∷ l ∷ []
  out (ifeq l)    = "ifeq" ∷ l ∷ []
  out (ifne l)    = "ifne" ∷ l ∷ []
  out (ifle l)    = "ifle" ∷ l ∷ []
  out (iflt l)    = "iflt" ∷ l ∷ []
  out (ifge l)    = "ifge" ∷ l ∷ []
  out (ifgt l)    = "ifgt" ∷ l ∷ []

  out iadd        = [ "iadd" ]
  out isub        = [ "isub"]
  out imul        = [ "imul" ]
  out idiv        = [ "idiv" ]
  out ixor        = [ "ixor" ]

  out (new c)     = "new" ∷ c ∷ []

data Stat : Set where
  label : String → Stat
  instr : Instr  → Stat

module Statement where

  out : Stat → List String
  out (label x) = x ∷ ":" ∷ []
  out (instr x) = Instruction.out x

record Method : Set where
  constructor method
  field
    name       : String
    descriptor : Desc
    body       : List Stat

  out : List String
  out = List.concat $
         (".method" ∷ "public" ∷ descriptor)
      ∷  List.concatMap Statement.out body
      ∷  []

record Jasmin : Set where
  constructor jasmin
  field
    header  : Header
    methods : List Method
  
  out : List String
  out = List.concat $
        Header.out header
      ∷ List.concatMap Method.out methods
      ∷ []
