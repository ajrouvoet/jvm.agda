{-# OPTIONS --safe #-}

{- A typeclass for converting between type disciplines #-}
module CF.Transform.Compile.ToJVM where

open import Level
open import Data.Product as P
open import Data.List as L
open import Data.List.Properties as LP
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Relation.Ternary.Morphisms

open import CF.Types  as CF
open import JVM.Types as JVM

record To {l r} (L : Set l) (R : Set r) : Set (l ⊔ r) where
  field
    ⟦_⟧ : L → R

open To {{...}} public

instance ⟦⟧-list : ∀ {a} {A B : Set a} {{_ : To A B}} → To (List A) (List B)
To.⟦_⟧ ⟦⟧-list = L.map ⟦_⟧

instance ⟦⟧-prod : ∀ {a} {A B C D : Set a} {{_ : To A B}} {{_ : To C D}} → To (A × C) (B × D)
To.⟦_⟧ ⟦⟧-prod = P.map ⟦_⟧ ⟦_⟧

instance cfToJvm-ty : To CF.Ty JVM.Ty
To.⟦_⟧ cfToJvm-ty = ‵_
  where
    ‵_ : CF.Ty → JVM.Ty
    ‵ void  = boolean
    ‵ int   = int
    ‵ bool  = boolean

instance cfToJvm-funty : To FunTy Fun
To.⟦ cfToJvm-funty ⟧ (n ∶ as ⟶ r) = n / "apply" :⟨ ⟦ as ⟧ ⟩ ty ⟦ r ⟧

instance cfToJvm-constant : To TopLevelDecl Constant
To.⟦ cfToJvm-constant ⟧ (fun fty) = staticfun ⟦ fty ⟧

instance cfToJvm-var : ∀ {ℓ} {A B : Set ℓ} {{_ : To A B}} {a : A} {as} →
                       To (a ∈ as) (⟦ a ⟧ ∈ ⟦ as ⟧)
To.⟦_⟧ cfToJvm-var = ∈-map⁺ ⟦_⟧

private
  module _ {t} {T : Set t} where
    open import JVM.Model T public

instance on-intf : ∀ {ℓ} {A B : Set ℓ} {{_ : To A B}} → To (Intf {T = A}) (Intf {T = B})
To.⟦ on-intf ⟧ (u ⇅ d) = ⟦ u ⟧ ⇅ ⟦ d ⟧
