{-# OPTIONS --safe --without-K #-}
module CF.Types where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary

data Ty : Set where
  void : Ty
  int  : Ty
  bool : Ty
  -- ref  : Ty → Ty

variable
  a b c r s t   : Ty
  as bs cs      : List Ty

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
