{-# OPTIONS --safe --without-K #-}
module JVM.Builtins where

open import Data.List

open import JVM.Types

Object = "java/lang/Object"

jre : Constantpool
jre = staticref ("java/lang/System"    / "out"     ∶ ref "java/io/PrintStream")
    ∷ virtual   ("java/io/PrintStream" / "println" :⟨ [ int ] ⟩ void)
    ∷ class     (Object)
    ∷ virtual   (Object / "<init>" :⟨ [] ⟩ void)
    ∷ []
