module JVM.Types where

open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary

data Ty : Set where
  void : Ty
  int  : Ty
  ref  : Ty → Ty

data Primitive : Ty → Set where
  int  : Primitive int
  void : Primitive void

variable
  a b r s t : Ty

World : Set
World = List Ty

_≟_ : Decidable (_≡_ {A = Ty})
void ≟ void = yes refl
void ≟ int = no (λ ())
void ≟ ref x = no (λ ())
int ≟ void = no (λ ())
int ≟ int = yes refl
int ≟ ref x = no (λ ())
ref x ≟ void = no (λ ())
ref x ≟ int = no (λ ())
ref x ≟ ref y with x ≟ y
ref x ≟ ref y | yes p = yes (cong ref p)
ref x ≟ ref y | no ¬p = no λ{ refl → ¬p refl }
