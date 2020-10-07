module CF.Examples.Ex1 where

open import Function
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.Nat
open import Data.String

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad.Possibly
open import Relation.Ternary.Data.Allstar
open import Relation.Ternary.Data.Bigstar hiding ([_])

open import CF.Types
open import CF.Syntax as Src
open import CF.Contexts.Lexical

open import JVM.Transform.Assemble
open import JVM.Printer
import JVM.Printer.Jasmin as J

ex₁ : Closed (Src.Block void)
ex₁ = ( 
  Src.while (
    Src.bool true ∙⟨ ∙-idˡ ⟩ Src.block 
    -- int j = true
    (Src.bool true ≔⟨ ∙-idˡ ⟩ Possibly.possibly ∼-all (
      Src.ifthenelse
        -- if j
        (var 
          ∙⟨ overlaps ∙-idˡ ⟩
          -- then
          Src.block (
            -- int i = j
            var ≔⟨ consˡ ∙-idˡ ⟩
            Possibly.possibly ∼-all (
              -- j := j
              Src.asgn (vars ∙⟨ overlaps ∙-idˡ ⟩ var) ⍮⟨ ∙-idʳ ⟩
              Src.run unit ⍮⟨ ∙-idʳ ⟩
              emp))
          -- else
          ∙⟨ overlaps ∙-idˡ ⟩
          Src.block (
            -- int i = j
            var ≔⟨ consˡ ∙-idˡ ⟩
            Possibly.possibly ∼-none (
              Src.run unit ⍮⟨ ∙-idʳ ⟩
              emp))
          )
        Src.⍮⟨ ∙-idʳ ⟩ emp
    ))) Src.⍮⟨ ∙-idʳ ⟩ emp)

open import IO as IO
open import Codata.Musical.Notation

open import CF.Compile

main = IO.run (putStrLn test)
  where
    test = Show.showBytecode $ proj₂ $ exec-extractor $ extract (proj₂ $ compile ex₁)

-- Uncomment this instead of the above main to output Jasmin code.
-- You can assemble this using Jasmin so that you can run the output with java.
-- Disclaimer: the jasmin compiler pass is not verified.
-- main = IO.run (putStrLn (J.unlines $ J.Jasmin.out proc))
--   where
--   proc = procedure "ex1" (proj₂ $ compile ex₁)
