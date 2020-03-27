{-# OPTIONS --safe --no-qualified-instances #-}
module JVM.Defaults.Syntax.Classes where

open import Level
open import Function
open import Data.Empty
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.String

open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Data.Bigstar hiding ([_])

open import JVM.Types
open import JVM.Builtins
open import JVM.Defaults.Syntax.Instructions
open import JVM.Compiler

module _ (T : Set) where
  open import JVM.Model T public using (Intf)

module _ {T : Set} where
  open import JVM.Model T public hiding (Intf; empty-rel; duplicate)

  instance list-empty : Emptiness {A = List T} []
  list-empty = record {}

[_]-stack : Ret → StackTy
[ ty a ]-stack = [ a ]
[ void ]-stack = []

VirtualBody : Fun → Pred Constantpool 0ℓ
VirtualBody (cls / name :⟨ as ⟩ r) 𝑪 = ⟪ 𝑪 , (ref cls ∷ as)  ∣ [] ⇒ [ r ]-stack ⟫ ε

StaticBody : Fun → Pred Constantpool 0ℓ
StaticBody (_ / _ :⟨ as ⟩ r) 𝑪 = ⟪ 𝑪 , as  ∣ [] ⇒ [ r ]-stack ⟫ ε

-- Implementation of class members
Impl : Constant → Pred Constantpool 0ℓ
Impl (class x)                                    = ∅ -- no inner/nested classes supported
Impl (fieldref x)                                 = ∅ -- todo
Impl (staticref x)                                = Emp
Impl (virtual fn)   = VirtualBody fn
Impl (staticfun fn) = StaticBody fn

-- Special initialization virtual
Init : String → Pred (Intf Constant) 0ℓ
Init cls = let init = cls / "<init>" :⟨ [] ⟩ void
         in Up (Just (virtual init))
          ⊙ Down (VirtualBody init)

Classname : String → Pred Constantpool 0ℓ
Classname cls = Just (class cls)

Funname : Fun → Pred Constantpool 0ℓ
Funname fn = Just (staticfun fn)

Class : Pred (Intf Constant) 0ℓ
Class = ⋃[ cls ∶ String ]
      ( Up (Classname cls)
      ⊙ Bigstar (⋃[ k ∶ Constant ] (Up (Just k) ⊙ Down (Impl k)))
      )

  where

-- Typesafe initializers require sub-typing (calling Object init on cls ref)
-- defaultInit : (cls : String) → VirtualBody (cls / "<init>" :⟨ [] ⟩ void) jre
-- defaultInit cls = execCompiler $ do
--   code (load (here refl))
--   refl ← code (invokespecial (there (there (there {!here refl!}))))
--   {!!}

functionClass : (fn : Fun) (open Fun fn)
               → ∀[ Down (StaticBody fn) ⇒ Class ⊙ Down (Classname cls ⊗ Funname fn) ]
functionClass fn@(cls / name :⟨ as ⟩ r) body =
  {!!}
  -- ( cls
  -- , ↑ refl            -- provide class
  -- ∙⟨ ∙-∙ ⟩ (staticfun fn , ↑ refl ∙⟨ ∙-∙ ⟩ body) ✴⟨ ∙-idʳ ⟩ emp)
  -- ∙⟨ ex sub-ε (sub {!^!} {!!}) {!!} {!!} ⟩ ↓ (refl ⊗⟨ Overlap.∙-∙ ⟩ refl) -- ref to defined function

  where open Overlap using (bags-isMonoid)
