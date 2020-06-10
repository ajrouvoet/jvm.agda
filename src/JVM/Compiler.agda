{-# OPTIONS --safe #-}
module JVM.Compiler where

open import JVM.Types
open import JVM.Defaults.Syntax.Instructions

module _ 𝑭 where
  open import JVM.Compiler.Monad StackTy ⟨ 𝑭 ∣_↝_⟩ noop using (Compiler) public

module _ {𝑭} where
  open import JVM.Compiler.Monad StackTy ⟨ 𝑭 ∣_↝_⟩ noop hiding (Compiler) public
