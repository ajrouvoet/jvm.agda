module CF.Examples.Ex2 where

open import Function
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.Nat
open import Data.String

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Separation
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad.Possibly

open import JVM.Contexts
open import JVM.Types

open import CF.Syntax as Src
open import CF.Compile

ex₂ : Src.Block bool ε
ex₂ =
                                         Src.num 0
    ≔⟨ ∙-idˡ ⟩ Possibly.possibly ∼-all ( Src.while (bop lt (var refl ∙⟨ ∙-idʳ ⟩ num 10)
    ∙⟨ overlaps ∙-idˡ ⟩                    Src.block (
                                             Src.asgn (refl ∙⟨ overlaps ∙-idˡ ⟩ bop add (var refl ∙⟨ ∙-idʳ ⟩ num 1))
    ⍮⟨ ∙-idʳ ⟩                              emp))
    ⍮⟨ ∙-idʳ ⟩ emp
  )

open import IO as IO
open import Codata.Musical.Notation
open import JVM.Defaults.Printer

main = IO.run (putStrLn (J.unlines $ J.Jasmin.out proc))
  where
  import JVM.Defaults.Printer.Jasmin as J
  proc = procedure "ex2" (proj₂ $ compile ex₂)
