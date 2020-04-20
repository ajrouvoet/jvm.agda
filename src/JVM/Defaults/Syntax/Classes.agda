{-# OPTIONS --no-qualified-instances #-}
module JVM.Defaults.Syntax.Classes where

open import Level
open import Function
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.String hiding (_++_)

open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Weakening
open import Relation.Ternary.Data.Bigstar as ⊛ hiding ([_])

open import JVM.Types
open import JVM.Builtins
open import JVM.Defaults.Syntax.Instructions
open import JVM.Compiler


-- [_]-stack : Ret → StackTy
-- [ ty a ]-stack = [ a ]
-- [ void ]-stack = []

-- VirtualBody : Fun → Pred Constantpool 0ℓ
-- VirtualBody (cls / name :⟨ as ⟩ r) 𝑪 =
--   ∃ λ locals →
--     ⟪ 𝑪 , ref cls ∷ (as ++ locals) ∣ [] ⇒ [] ⟫ ε

-- StaticBody : Fun → Pred Constantpool 0ℓ
-- StaticBody (_ / _ :⟨ as ⟩ r) 𝑪       =
--   ∃ λ locals →
--     ⟪ 𝑪 , as ++ locals             ∣ [] ⇒ [] ⟫ ε

-- -- Implementation of class members
-- Impl : Constant → Pred Constantpool 0ℓ
-- Impl (class x)      = ∅ -- no inner/nested classes supported
-- Impl (fieldref x)   = ∅ -- todo
-- Impl (staticref x)  = Emp
-- Impl (virtual fn)   = VirtualBody fn
-- Impl (staticfun fn) = StaticBody fn

-- -- Special initialization virtual
-- Init : String → Pred (Intf Constant) 0ℓ
-- Init cls = let init = cls / "<init>" :⟨ [] ⟩ void
--          in Up (Just (virtual init))
--           ✴ Down (VirtualBody init)

-- Classname : String → Pred Constantpool 0ℓ
-- Classname cls = Just (class cls)

-- Funname : Fun → Pred Constantpool 0ℓ
-- Funname fn = Just (staticfun fn)

-- Main : Pred Constantpool 0ℓ
-- Main = ⋃[ cls ∶ _ ] Just (staticfun (cls / "main" :⟨ array (ref Str) ∷ [] ⟩ void))

-- Member : Pred (Intf Constant) 0ℓ
-- Member = ⋃[ k ∶ Constant ] (Up (Just k) ✴ Down (Impl k))

-- mkMember : ∀ k → ∀[ (Up (Just k) ✴ Down (Impl k)) ⇒ Member ]
-- mkMember k = k ,_

-- -- Optional declaration of the class
-- Classdecl = λ cls → Up (Classname cls) ∪ Emp
-- pattern nodecl = inj₂ refl

-- Class : Pred (Intf Constant) 0ℓ
-- Class = ⋃[ cls ∶ String ]
--       ( Classdecl cls
--       ✴ Bigstar Member 
--       )

-- mkClass : ∀ cls → ∀[ ( Classdecl cls ✴ Bigstar Member) ⇒ Class ]
-- mkClass c = c ,_

-- Classes = Bigstar Class

-- Program : Set
-- Program = Down⁻ ((Down Main ✴ Classes) ⇑) jre

-- functionClass : (fn : Fun) (open Fun fn)
--               → ∀[ Down (StaticBody fn) ⇒ Class ✴ Down (Funname fn) ]
-- functionClass fn body = 
--   let
--     open Fun fn
--     kind                 = staticfun fn
--     f↓∙[f↑∙b]            = ✴-assocᵣ $ (✴-swap $ binder kind) ∙⟨ ∙-idˡ ⟩ body
--     f↓∙members           = ⟨ id ⟨✴⟩ (⊛.[_] ∘ mkMember kind) ⟩ f↓∙[f↑∙b]
--   in ⟨ (λ m → mkClass name (nodecl ∙⟨ ∙-idˡ ⟩ m)) ⟨✴⟩ id ⟩ (✴-swap f↓∙members)

-- -- Typesafe initializers require sub-typing (calling Object init on cls ref)
-- -- defaultInit : (cls : String) → VirtualBody (cls / "<init>" :⟨ [] ⟩ void) jre
-- -- defaultInit cls = execCompiler $ do
-- --   code (load (here refl))
-- --   refl ← code (invokespecial (there (there (there {!here refl!}))))
-- --   {!!}
