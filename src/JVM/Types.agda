{-# OPTIONS --safe --without-K #-}
module JVM.Types where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.List
open import Data.String

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary

-- Primitive types
data Ty : Set where
  boolean                   : Ty
  byte short int long char  : Ty
  ref                       : String → Ty
  array                     : Ty → Ty

data Ret : Set where
  ty   : Ty → Ret
  void : Ret      -- clearly void is not a type... right? (Spec accurate)

IsIntegral : Ty → Set
IsIntegral boolean = ⊤ -- int instructions compatible with boolean
IsIntegral byte    = ⊤
IsIntegral short   = ⊤
IsIntegral int     = ⊤
IsIntegral long    = ⊤
IsIntegral char    = ⊤
IsIntegral _       = ⊥

StackTy  = List Ty
LocalsTy = List Ty
Labels   = List StackTy

record StaticFun : Set where
  constructor _/_:⟨_⟩_
  field
    cls     : String
    name    : String
    sf_args : List Ty
    sf_ret  : Ret

data Constant : Set where
  classref  : String → Constant
  fieldref  : String → Ty → Constant
  staticref : String → Ty → Constant -- in the actual constant pool static fields are fields
  staticfun : StaticFun → Constant

Constantpool = List Constant
FrameTy      = Constantpool × LocalsTy

variable
  𝑪               : Constantpool
  𝑹₁ 𝑹₂ 𝑹₃ 𝑹₄ 𝑹 : LocalsTy
  𝑭₁ 𝑭₂ 𝑭₃ 𝑭₄ 𝑭  : FrameTy
  𝑐 𝑑 𝑒           : String
  a b c r s t     : Ty
  as bs cs        : List Ty
  ψ₁ ψ₂ ψ₃ ψ      : StackTy  -- stack typings

-- data Primitive : Ty → Set where
--   int  : Primitive int
--   void : Primitive void

-- World : Set
-- World = List Ty

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

-- {- Frames and their typings -}
-- module _ where

--   RegTy    = Ty

--   variable
--     ψ₁ ψ₂ ψ₃ ψ : StackTy  -- stack typings
--     τ₁ τ₂ τ₃ τ : LocalsTy -- register file typings

--   record FrameTy : Set where
--     constructor ⟨_,_⟩
--     field
--       locals-ty : List RegTy
--       stack-ty  : List Ty
