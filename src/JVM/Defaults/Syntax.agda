open import MJ.Classtable

module JVM.Defaults.Syntax {c}(Σ : Classtable c) where

open import MJ.Types c public
open import JVM.Defaults.Syntax.Frames Σ public
open import JVM.Defaults.Syntax.Bytecode Σ public hiding (Split)
