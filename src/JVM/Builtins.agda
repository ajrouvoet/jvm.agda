module JVM.Builtins where

open import Data.List

open import JVM.Types
open import JVM.Model StackTy
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions

jre : Constantpool
jre = staticref ("java/lang/System"    / "out"     ∶ ref "java/io/PrintStream")
    ∷ virtual   ("java/io/PrintStream" / "println" :⟨ [ int ] ⟩ void)
    ∷ []
