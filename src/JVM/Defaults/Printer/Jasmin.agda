module JVM.Defaults.Printer.Jasmin where

open import Function
open import Data.Nat
open import Data.Nat.Show as NatShow
open import Data.String as S using (String)
open import Data.List as List

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

Desc : Set
Desc = List String

module Descriptor where

  out : Desc → String
  out d with reverse d
  ... | []     = "()V"
  ... | r ∷ d' = args d' S.++ r
    where
      args : Desc → String
      args d = "(" S.++ (S.intersperse ";" d) S.++ ")"

data Instr : Set where
  nop pop dup swap ret : Instr

  aconst_null   : Instr
  bipush sipush : ℕ → Instr
  iconstm1 iconst0 iconst1 iconst2 : Instr

  aload iload   : ℕ → Instr
  astore istore : ℕ → Instr

  new           : String → Instr

  ifeq ifne ifle iflt ifge ifgt goto : String → Instr

  iadd isub imul idiv ixor : Instr

  invokespecial invokestatic : String → String → Desc → Instr
  
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
  out (iload n)   = unwords $ "iload"  ∷ NatShow.show n ∷ []
  out (astore n)  = unwords $ "astore" ∷ NatShow.show n ∷ []
  out (istore n)  = unwords $ "istore" ∷ NatShow.show n ∷ []

  out iconstm1    = line "iconstm1"
  out iconst0     = line "iconst_0"
  out iconst1     = line "iconst_1"
  out iconst2     = line "iconst_2"

  out (goto l)    = unwords $ "goto" ∷ lbl l ∷ []
  out (ifeq l)    = unwords $ "ifeq" ∷ lbl l ∷ []
  out (ifne l)    = unwords $ "ifne" ∷ lbl l ∷ []
  out (ifle l)    = unwords $ "ifle" ∷ lbl l ∷ []
  out (iflt l)    = unwords $ "iflt" ∷ lbl l ∷ []
  out (ifge l)    = unwords $ "ifge" ∷ lbl l ∷ []
  out (ifgt l)    = unwords $ "ifgt" ∷ lbl l ∷ []

  out iadd        = line "iadd" 
  out isub        = line "isub"
  out imul        = line "imul" 
  out idiv        = line "idiv" 
  out ixor        = line "ixor" 

  out (new c)     = unwords $ "new" ∷ c ∷ []

  out (invokespecial c m d) = unwords $ "invokespecial" ∷ (c S.++ "/" S.++ m S.++ Descriptor.out d) ∷ [] 
  out (invokestatic  c m d) = unwords $ "invokestatic"  ∷ (c S.++ "/" S.++ m S.++ Descriptor.out d) ∷ []

data Stat : Set where
  label : String → Stat
  instr : Instr  → Stat

module Statement where

  out : Stat → Line
  out (label x) = line $ Instruction.lbl x S.++ ":"
  out (instr x) = Instruction.out x

record Method : Set where
  constructor method
  field
    name       : String
    access     : List String
    locals     : ℕ
    stacksize  : ℕ
    descriptor : Desc
    body       : List Stat

  out : Lines
  out =  (unwords $ ".method" ∷ (S.unwords access) ∷ (name S.++ Descriptor.out descriptor) ∷ [])
      <+ (ident $ unwords $ ".limit locals" ∷ NatShow.show locals ∷ [])
      <+ (ident $ unwords $ ".limit stack"  ∷ NatShow.show stacksize ∷ [])
      <+ (lines $ List.map (ident ∘ Statement.out) body)
      +> (line $ ".end method")

record Jasmin : Set where
  constructor jasmin
  field
    header  : Header
    methods : List Method
  
  out : Lines
  out = Header.out header <> pars (List.map Method.out methods)

module _ where

  procedure : (name : String) → ℕ → ℕ → List Stat → Jasmin
  procedure name locals stack st =
    jasmin
      (record { class_spec = class name ; super_spec = super "java/lang/Object" })
      ( method "apply" ("public" ∷ "static" ∷ []) locals stack [] (st ∷ʳ instr ret)
      ∷ method "<init>" [ "public" ] 1 1 [] 
        ( instr (aload 0)
        ∷ instr (invokespecial "java/lang/Object" "<init>" [])
        ∷ instr ret
        ∷ []
        )
      ∷ method "main" ("public" ∷ "static" ∷ []) 1 0 ("[Ljava/lang/String;" ∷ "V" ∷ [] )
        ( instr (invokestatic name "apply" [])
        ∷ instr ret
        ∷ []
        )
      ∷ []
      )
