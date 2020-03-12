module CF.Examples.Ex1 where

open import Data.Product
open import Data.List

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Separation
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Possibly
open import Relation.Ternary.Monad.Weakening

open import JVM.Contexts
open import JVM.Types

open import CF.Syntax as Src
open import CF.Transform.Hoist
open import CF.Compile

ex₁ : Src.Block int ε
ex₁ = ( 
  -- int j = 42
  Src.num 42 ≔⟨ ∙-idˡ ⟩ Possibly.possibly ∼-all (
    Src.ifthenelse
      (var refl
        ×⟨ overlaps ∙-idˡ ⟩
        -- then
        Src.block (
          -- int i = j
          var refl ≔⟨ consˡ ∙-idˡ ⟩
          Possibly.possibly ∼-all (
            Src.ret (var refl) Src.⍮⟨ ∙-idʳ ⟩
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
  ))

open import JVM.Defaults.Syntax.Instructions.Show

ex₁-hoisted  = hoist ex₁
ex₁-bytecode =
  let
    (_ , Possibly.possibly _ ex) = ex₁-hoisted
    (bc ∙⟨ _ ⟩ _) = compiler [] (return ex)
  in bc
