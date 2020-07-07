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

variable
  a b c r s t   : Ty
  as bs cs      : List Ty
