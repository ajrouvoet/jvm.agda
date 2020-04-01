{-# OPTIONS --no-qualified-instances --rewriting #-}
module CF.Transform.Compile.Programs where

open import Function
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.List as List hiding (null; [_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Weakening
open import Relation.Ternary.Data.Bigstar
open import Relation.Ternary.Morphisms

open import CF.Syntax.DeBruijn as CF
open import CF.Transform.Compile.Expressions
open import CF.Types
open import CF.Builtins
open import CF.Transform.Compile.ToJVM
open import CF.Transform.Compile.ToJVM.Rewriting
open import CF.Transform.Compile.Statements

open import JVM.Types
open import JVM.Builtins
open import JVM.Compiler
open import JVM.Contexts
open import JVM.Defaults.Syntax.Values
open import JVM.Defaults.Syntax.Instructions
open import JVM.Defaults.Syntax.Classes as JVM

module _ {T : Set} where
  open import JVM.Model T public
  open Overlap public

open import Data.List.Relation.Unary.All
postulate ⟦builtins⟧'' : All (λ tl → Impl ⟦ tl ⟧ jre) builtins

open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

module _ {A B : Set} (a→b : A → B) where

  m : Morphism {A = List A} {B = List B} Overlap.bags-isMonoid Overlap.bags-isMonoid
  Morphism.j m     = List.map a→b
  Morphism.jcong m = map⁺ a→b
  Morphism.j-ε m   = ↭-refl
  Morphism.j-∙ m   = {!!}
  Morphism.j-∙⁻ m  = {!!}

mi : Morphism {A = Intf {T = TopLevelDecl}} {B = Intf {T = Constant}} intf-isMonoid intf-isMonoid
mi = {!!}

open Morphism mi

compile-function : ∀[ Function ⇒ⱼ Class ]
compile-function (function c (↑ refl) σ body) =
  let 
    body-code = execCompiler $ compiler [] (proj₂ body)
    fc        = functionClass ⟦ c ⟧ (↓ (-, body-code))
  in {!fc!}

-- compile-program : CF.Program → JVM.Program
-- compile-program (program main σ fs globals) =
--   let
--     jayz = ⊛-map {!!} fs
--   in
--   (↓ {!⟦ main ⟧!} ∙⟨ {!!} ⟩ {!!}) ⇈ {!!}
