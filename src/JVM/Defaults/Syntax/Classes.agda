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
open import Relation.Ternary.Monad.Identity using (module Wrapped); open Wrapped
open import Relation.Ternary.Data.Bigstar as ⊛ hiding ([_])

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

Member : Pred (Intf Constant) 0ℓ
Member = ⋃[ k ∶ Constant ] (Up (Just k) ⊙ Down (Impl k))

mkMember : ∀ k → ∀[ (Up (Just k) ⊙ Down (Impl k)) ⇒ Member ]
mkMember k = k ,_

Class : Pred (Intf Constant) 0ℓ
Class = ⋃[ cls ∶ String ]
      ( Up (Classname cls)
      ⊙ Bigstar Member 
      )

mkClass : ∀ cls → ∀[ ( Up (Classname cls) ⊙ Bigstar Member) ⇒ Class ]
mkClass c = c ,_

functionClass : (fn : Fun) (open Fun fn)
              → ∀[ Down (StaticBody fn) ⇒ Class ⊙ Down (Classname cls ⊗ Funname fn) ]
functionClass fn body = 
  let
    open Fun fn
    kind                 = staticfun fn
    f↓∙[f↑∙b]            = ⊙-assocᵣ $ (⊙-swap $ binder kind) ∙⟨ ∙-idˡ ⟩ body
    f↓∙members           = ⟨ id ⟨⊙⟩ (⊛.[_] ∘ mkMember kind) ⟩ f↓∙[f↑∙b]
    c↑∙[c↓∙[f↓∙members]] = ⊙-assocᵣ $ binder (class cls) ∙⟨ ∙-idˡ ⟩ f↓∙members
    [c↑∙members]∙[c↓∙f↓] = ⊙-assocₗ $ ⟨ id ⟨⊙⟩ ⊙-rotateᵣ ⟩ c↑∙[c↓∙[f↓∙members]]
  in ⟨ mkClass cls ⟨⊙⟩ zipDown ⟩ [c↑∙members]∙[c↓∙f↓]

-- Typesafe initializers require sub-typing (calling Object init on cls ref)
-- defaultInit : (cls : String) → VirtualBody (cls / "<init>" :⟨ [] ⟩ void) jre
-- defaultInit cls = execCompiler $ do
--   code (load (here refl))
--   refl ← code (invokespecial (there (there (there {!here refl!}))))
--   {!!}
