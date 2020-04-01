module CF.Examples.Ex1 where

open import Function
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.Nat
open import Data.String

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad.Possibly
open import Relation.Ternary.Data.Allstar
open import Relation.Ternary.Data.Bigstar hiding ([_])

-- open import JVM.Contexts

open import CF.Types
open import CF.Syntax as Src
open import CF.Contexts

module _ {T : Set} where
  open import Relation.Ternary.Construct.List.Overlapping T public

open import CF.Builtins

main-fun : Closed (Src.Block void) [ print ]
main-fun = ( 
  Src.while (
    Src.bool true ∙⟨ ∙-idˡ ⟩ Src.block 
    -- int j = 42
    (Src.bool true ≔⟨ ∙-idˡ ⟩ Possibly.possibly ∼-all (
      Src.ifthenelse
        -- if j != 0
        (var 
          ∙⟨ ∙-idˡ , overlaps ∙-idˡ ⟩
          -- then
          Src.block (
            -- int i = j
            var ≔⟨ ∙-idˡ , consˡ ∙-idˡ ⟩
            Possibly.possibly ∼-all (
              -- j := j
              Src.asgn (vars ∙⟨ ∙-idˡ , overlaps ∙-idˡ ⟩ var)                                 ⍮⟨ ∙-idˡ , ∙-idʳ ⟩
              Src.run (Src.call (fn ∙⟨ ^ consˡ ∙-idˡ , ∙-idˡ ⟩ cons (num 42 ∙⟨ ∙-idʳ ⟩ nil))) ⍮⟨ ∙-idʳ ⟩
              emp))
          -- else
          ∙⟨ ∙-idʳ , overlaps ∙-idˡ ⟩
          Src.block (
            -- int i = j
            var ≔⟨ ∙-idˡ , consˡ ∙-idˡ ⟩
            Possibly.possibly ∼-none (
              Src.ret unit ⍮⟨ ∙-idʳ ⟩
              emp))
          )
        Src.⍮⟨ ∙-idʳ ⟩ emp
    ))) Src.⍮⟨ ∙-idʳ ⟩ emp)

open import IO as IO
open import Codata.Musical.Notation
open import JVM.Defaults.Printer

open import CF.Compile

main = IO.run (putStrLn (J.unlines $ J.Jasmin.out proc))
  where
  import JVM.Defaults.Printer.Jasmin as J
  proc = procedure "ex1" (proj₂ $ compile main-fun)

-- program : Program
-- program = ↓ refl
--         ∙⟨ {!!} ⟩ ((("main" , [] ⟶ void) , ↑ refl ∙⟨ {!!} ⟩ ↓ (Possibly.possibly ∼-all main-fun))
--         ✴⟨ {!!} ⟩ ((("print" , [ int ] ⟶ void) , {!!})
--         ✴⟨ {!!} ⟩ emp))
