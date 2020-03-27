{-# OPTIONS --safe --without-K #-}
module CF.Types where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product
open import Data.List as L
open import Data.String
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary

data Ty : Set where
  void : Ty
  int  : Ty
  bool : Ty
  -- ref  : Ty → Ty

record FunTy : Set where
  constructor _⟶_
  field
    argtys : List Ty
    retty  : Ty

data TopLevelTy : Set where
  fun : FunTy → TopLevelTy

TopLevelDecl = String × TopLevelTy

Globals : Set
Globals = List TopLevelDecl


Lex = List Ty

Ctx : Set
Ctx = Globals × Lex

_⍮_ : Ctx → List Ty → Ctx
(X , Γ) ⍮ Δ = (X , Δ L.++ Γ)

variable
  a b c r s t   : Ty
  as bs cs      : List Ty
  𝑓 𝑔 ℎ : String
  K K₁ K₂ K₃ K₄ : Ctx
  Δ Δ₁ Δ₂ : List Ty

-- _≟_ : Decidable (_≡_ {A = Ty})
-- void ≟ void = yes refl
-- void ≟ int = no (λ ())
-- void ≟ ref x = no (λ ())
-- int ≟ void = no (λ ())
-- int ≟ int = yes refl
-- int ≟ ref x = no (λ ())
-- ref x ≟ void = no (λ ())
-- ref x ≟ int = no (λ ())
-- ref x ≟ ref y with x ≟ y
-- ref x ≟ ref y | yes p = yes (cong ref p)
-- ref x ≟ ref y | no ¬p = no λ{ refl → ¬p refl }
-- void ≟ bool = no (λ ())
-- int ≟ bool = no (λ ())
-- bool ≟ void = no (λ ())
-- bool ≟ int = no (λ ())
-- bool ≟ bool = yes refl
-- bool ≟ ref y = no (λ ())
-- ref x ≟ bool = no (λ ())
