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

IsIntegral : Ty → Set
IsIntegral boolean = ⊤ -- int instructions compatible with boolean
IsIntegral byte    = ⊤
IsIntegral short   = ⊤
IsIntegral int     = ⊤
IsIntegral long    = ⊤
IsIntegral char    = ⊤

StackTy  = List Ty
LocalsTy = List Ty
Labels   = List StackTy

FrameTy      = LocalsTy

variable
  𝑹₁ 𝑹₂ 𝑹₃ 𝑹₄ 𝑹  : LocalsTy
  𝑭₁ 𝑭₂ 𝑭₃ 𝑭₄ 𝑭  : FrameTy
  a b c r s t      : Ty
  as bs cs         : List Ty
  ψ₁ ψ₂ ψ₃ ψ      : StackTy  -- stack typings
