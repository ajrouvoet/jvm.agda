module CF.Examples.Ex1 where

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
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Possibly
open import Relation.Ternary.Monad.Weakening

open import JVM.Contexts
open import JVM.Types
open import JVM.Defaults.Syntax.Instructions
open import JVM.Defaults.Transform.Noooops

open import CF.Syntax as Src
open import CF.Transform.Hoist
open import CF.Compile

ex₁ : Src.Statement bool ε
ex₁ = ( 
  Src.while (
    Src.bool true ∙⟨ ∙-idˡ ⟩ Src.block 
    -- int j = 42
    (Src.bool true ≔⟨ ∙-idˡ ⟩ Possibly.possibly ∼-all (
      Src.ifthenelse
        -- if j != 0
        (var refl
          ×⟨ overlaps ∙-idˡ ⟩
          -- then
          Src.block (
            -- int i = j
            var refl ≔⟨ consˡ ∙-idˡ ⟩
            Possibly.possibly ∼-all (
              -- j := j
              Src.asgn (refl ∙⟨ overlaps ∙-idˡ ⟩ var refl) Src.⍮⟨ ∙-idʳ ⟩
              emp))
          -- else
          ×⟨ overlaps [] ⟩
          Src.block (
            -- int i = j
            var refl ≔⟨ consˡ ∙-idˡ ⟩
            Possibly.possibly ∼-all (
              Src.ret (var refl) Src.⍮⟨ ∙-idʳ ⟩
              emp))
          )
        Src.⍮⟨ ∙-idʳ ⟩ emp
    ))))

open import JVM.Defaults.Printer

ex₁-hoisted  = translate ex₁
ex₁-bytecode =
  let
    (_ , Possibly.possibly _ ex) = ex₁-hoisted
    (bc ∙⟨ _ ⟩ _) = compile {ψ = []} (return ex)
  in bc

ex₁-optimized = noooop ex₁-bytecode

open import IO as IO
open import Data.String.Base using (_++_)
open import Codata.Musical.Notation
open import Data.Sum

main = IO.run (putStrLn (J.unlines $ J.Jasmin.out proc))
  where
  import JVM.Defaults.Printer.Jasmin as J
  proc = procedure "ex1" ex₁-optimized
