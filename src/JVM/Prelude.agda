{-# OPTIONS --safe --without-K #-}
module JVM.Prelude where

open import Level public hiding (zero) renaming (suc to sucℓ)
open import Function public using (case_of_; _∘_; id; const)

open import Data.List using (List; _∷_; []; [_]) public
open import Data.Unit using (⊤; tt) public
open import Data.Nat using (ℕ; suc; zero; _+_) public
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _⊕_)public
open import Data.Product public hiding (map; zip)

open import Relation.Unary hiding (_∈_; Empty) public
open import Relation.Binary.PropositionalEquality hiding ([_]) public

open import Relation.Ternary.Separation public
open import Relation.Ternary.Structures public
