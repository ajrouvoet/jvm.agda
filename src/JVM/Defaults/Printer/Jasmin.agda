module JVM.Defaults.Printer.Jasmin where

open import Function
open import Data.Nat
open import Data.Nat.Show as NatShow
open import Data.String as S using (String)
open import Data.List as List

open import JVM.Types
open import JVM.Builtins

sep : List (List String) → List String
sep = List.concat ∘ List.intersperse [ " " ]

Words = List String

abstract
  Line  = String
  Lines = List String

  unwords : Words → Line
  unwords = S.unwords

  line : String → Line
  line = id

  lines : List Line → Lines
  lines = id

  unlines : Lines → String
  unlines = S.unlines

  infixr 4 _<+_
  _<+_ : Line → Lines → Lines
  l <+ ls = l ∷ ls

  infixl 6 _+>_
  _+>_ : Lines → Line → Lines
  ls +> l = ls ∷ʳ l

  infixl 4 _<>_
  _<>_ : Lines → Lines → Lines
  ls <> js = ls ++ js

  pars : List Lines → Lines
  pars = concat

  ident : Line → Line
  ident = "\t" S.++_

  indent : Lines → Lines
  indent = List.map ident

record ClassSpec : Set where
  constructor class
  field
    class_name : String

  out : Line
  out = unwords $ ".class" ∷ "public" ∷ class_name ∷ []

record SuperSpec : Set where
  constructor super
  field
    class_name : String

  out : Line
  out = unwords  $ ".super" ∷ class_name ∷ []

record Header : Set where
  field
    class_spec : ClassSpec
    super_spec : SuperSpec

  out : Lines
  out = lines $ ClassSpec.out class_spec
      ∷ SuperSpec.out super_spec
      ∷ []

module Descriptor where

  type-desc : Ty → String
  type-desc boolean   = "Z"
  type-desc byte      = "B"
  type-desc short     = "S"
  type-desc int       = "I"
  type-desc long      = "J"
  type-desc char      = "C"
  type-desc (array t) = "[" S.++ type-desc t
  type-desc (ref cls) = S.concat $ "L" ∷ cls ∷ ";" ∷ []

  ret-desc : Ret → String
  ret-desc void   = "V"
  ret-desc (ty t) = type-desc t

  out : List Ty → Ret → String
  out as r = args as S.++ ret-desc r
    where
      args : List Ty → String
      args d = "(" S.++ (S.intersperse ";" (List.map type-desc d)) S.++ ")"

data Comparator : Set where
  eq ne lt ge gt le : Comparator
  icmpge icmpgt icmpeq icmpne icmplt icmple : Comparator

open import JVM.Types using (Fun)

module Comp where

  out : Comparator → String
  out eq = "eq"
  out ne = "ne"
  out lt = "lt"
  out ge = "ge"
  out gt = "gt"
  out le = "le"
  out icmpge = "_icmpge"
  out icmpgt = "_icmpgt"
  out icmpeq = "_icmpeq"
  out icmpne = "_icmpne"
  out icmplt = "_icmplt"
  out icmple = "_icmple"

data Instr : Set where
  nop pop dup swap ret : Instr

  aconst_null                      : Instr
  bipush sipush                    : ℕ → Instr
  iconstm1 iconst0 iconst1 iconst2 : Instr

  aaload  aload  iload             : ℕ → Instr
  aastore astore istore            : ℕ → Instr

  new                              : String → Instr

  goto                             : String     → Instr
  if                               : Comparator → String → Instr

  iadd isub imul idiv ixor         : Instr

  invokevirtual invokespecial invokestatic : Fun → Instr

module Funs where

  out : Fun → String
  out (c / m :⟨ as ⟩ r) = c S.++ "/" S.++ m S.++ Descriptor.out as r
  
module Instruction where

  lbl : String → String
  lbl x = "label_" S.++ x

  out : Instr → Line
  out nop         = line "nop" 
  out pop         = line "pop" 
  out dup         = line "dup" 
  out swap        = line "swap" 
  out ret         = line "return" 
  out aconst_null = line "aconst_null" 

  out (bipush n)  = unwords $ "sipush" ∷ NatShow.show n ∷ []
  out (sipush n)  = unwords $ "bipush" ∷ NatShow.show n ∷ []
  out (aload n)   = unwords $ "aload"  ∷ NatShow.show n ∷ []
  out (astore n)  = unwords $ "astore" ∷ NatShow.show n ∷ []
  out (iload n)   = unwords $ "iload"  ∷ NatShow.show n ∷ []
  out (istore n)  = unwords $ "istore" ∷ NatShow.show n ∷ []
  out (aaload n)  = unwords $ "aaload" ∷ NatShow.show n ∷ []
  out (aastore n) = unwords $ "astore" ∷ NatShow.show n ∷ []

  out iconstm1    = line "iconstm1"
  out iconst0     = line "iconst_0"
  out iconst1     = line "iconst_1"
  out iconst2     = line "iconst_2"

  out (goto l)    = unwords $ "goto" ∷ lbl l ∷ []
  out (if c l)    = unwords $ ("if" S.++ Comp.out c) ∷ lbl l ∷ []

  out iadd        = line "iadd" 
  out isub        = line "isub"
  out imul        = line "imul" 
  out idiv        = line "idiv" 
  out ixor        = line "ixor" 

  out (new c)     = unwords $ "new" ∷ c ∷ []

  out (invokespecial sf) = unwords $ "invokespecial" ∷ Funs.out sf ∷ [] 
  out (invokestatic  sf) = unwords $ "invokestatic"  ∷ Funs.out sf ∷ []
  out (invokevirtual sf) = unwords $ "invokevirtual" ∷ Funs.out sf ∷ []

data Stat : Set where
  label : String → Stat
  instr : Instr  → Stat

module Statement where

  out : Stat → Line
  out (label x) = line $ Instruction.lbl x S.++ ":"
  out (instr x) = Instruction.out x

record ClassField : Set where
  constructor clsfield
  field
    name   : String
    access : List String
    f_ty   : Ty

  out : Line
  out = unwords
      $ ".field"
      ∷ access
     ++ name
      ∷ Descriptor.type-desc f_ty
      ∷ []

record Method : Set where
  constructor method
  field
    name       : String
    access     : List String
    locals     : ℕ
    stacksize  : ℕ
    m_args     : List Ty
    m_ret      : Ret
    body       : List Stat

  out : Lines
  out =  (unwords $ ".method" ∷ (S.unwords access) ∷ (name S.++ Descriptor.out m_args m_ret) ∷ [])
      <+ (ident $ unwords $ ".limit locals" ∷ NatShow.show locals ∷ [])
      <+ (ident $ unwords $ ".limit stack"  ∷ NatShow.show stacksize ∷ [])
      <+ (lines $ List.map (ident ∘ Statement.out) body)
      +> (line $ ".end method")

record Jasmin : Set where
  constructor jasmin
  field
    header  : Header
    fields  : List ClassField
    methods : List Method
  
  out : Lines
  out = Header.out header
      <> lines (List.map ClassField.out fields)
      <> pars (List.map Method.out methods)

module _ where

  procedure : (name : String) → ℕ → ℕ → List Stat → Jasmin
  procedure name locals stack st =
    jasmin
      (record { class_spec = class name ; super_spec = super Object })
      []
      ( method "apply" ("public" ∷ "static" ∷ []) locals stack [] void (st ∷ʳ instr ret)
      ∷ method "<init>" [ "public" ] 1 1 [] void
        ( instr (aload 0)
        ∷ instr (invokespecial ("java/lang/Object" / "<init>" :⟨ [] ⟩ void))
        ∷ instr ret
        ∷ []
        )
      ∷ method "main" ("public" ∷ "static" ∷ []) 1 0 [ array (ref "java/lang/String") ] void
        ( instr (invokestatic (name / "apply" :⟨ [] ⟩ void))
        ∷ instr ret
        ∷ []
        )
      ∷ []
      )
