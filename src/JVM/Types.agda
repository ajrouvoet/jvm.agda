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

Integer = ref "java/lang/Integer"
Boolean = ref "java/lang/Boolean"

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

_:?:_ : Ret → StackTy → StackTy
ty a :?: ψ = a ∷ ψ
void :?: ψ = ψ

record Fun : Set where
  constructor _/_:⟨_⟩_
  field
    cls     : String
    name    : String
    sf_args : List Ty
    sf_ret  : Ret

record Fld : Set where
  constructor _/_∶_
  field
    fld_cls  : String
    fld_name : String
    fld_ty   : Ty

data Constant : Set where
  class     : String → Constant
  fieldref  : Fld → Constant
  staticref : Fld → Constant -- in the actual constant pool static fields are fields
  virtual   : Fun → Constant
  staticfun : Fun → Constant

Constantpool = List Constant
FrameTy      = LocalsTy

variable
  𝑪                : Constantpool
  𝑹₁ 𝑹₂ 𝑹₃ 𝑹₄ 𝑹  : LocalsTy
  𝑭₁ 𝑭₂ 𝑭₃ 𝑭₄ 𝑭  : FrameTy
  𝑎 𝑏              : Fld
  𝑐 𝑛 𝑚           : String
  𝑓 𝑔              : Fun
  a b c r s t      : Ty
  as bs cs         : List Ty
  ψ₁ ψ₂ ψ₃ ψ      : StackTy  -- stack typings
