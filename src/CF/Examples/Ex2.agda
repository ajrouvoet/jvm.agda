module CF.Examples.Ex2 where

open import Function
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.Integer
open import Data.String

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad.Possibly

open import JVM.Contexts
open import JVM.Types
open import JVM.Transform.Assemble

open import JVM.Printer
import JVM.Printer.Jasmin as J

open import CF.Syntax as Src
open import CF.Types
open import CF.Contexts.Lexical
open import CF.Compile

-- int i = 0;
-- while(i < 10) {
--   i = i + 1
-- }
ex₂ : Src.Block void ε
ex₂ =
    Src.num (+ 0) ≔⟨ ∙-idˡ ⟩ Possibly.possibly ∼-all (
    Src.while (bop gt (var ∙⟨ ∙-idʳ ⟩ num (+ 10)) ∙⟨ overlaps ∙-idˡ ⟩
      Src.block (
        Src.asgn (refl ∙⟨ overlaps ∙-idˡ ⟩ bop add (var ∙⟨ ∙-idʳ ⟩ num (+ 1))) ⍮⟨ ∙-idʳ ⟩ 
        emp)
    )⍮⟨ ∙-idʳ ⟩ emp
  )
  
-- Which should compile to:
--
-- 0: push 0
-- 1: store 0
-- 2: load 0
-- 3: push 10
-- 4: if_icmplt 7
-- 5: push false // 0
-- 6: goto 8
-- 7: push true  // 1
-- 8: if eq 14   // 0 = false -> jump to end
-- 9: load 0
-- 10: push 1
-- 11: bop add
-- 12: store 0
-- 13: goto 2
-- 14: nop

open import IO as IO
main = IO.run (putStrLn test)
  where
    test = Show.showBytecode $ proj₂ $ exec-extractor $ extract (proj₂ $ compile ex₂)

-- Uncomment this instead of the above main to output Jasmin code.
-- You can assemble this using Jasmin so that you can run the output with java.
-- Disclaimer: the jasmin compiler pass is not verified.
-- main = IO.run (putStrLn (J.unlines $ J.Jasmin.out proc))
--   where
--   proc = procedure "ex1" (proj₂ $ compile ex₂)
