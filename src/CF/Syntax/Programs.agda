{-# OPTIONS --safe #-}
open import Level
open import Data.List
open import CF.Types
open import Relation.Unary hiding (_⊢_)

module CF.Syntax.Programs (Body : (args : List Ty) → Ty → Pred Globals 0ℓ) where

open import Data.Product
open import Data.String

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Data.Bigstar
open import Relation.Ternary.Monad.Weakening

open import CF.Builtins
open import CF.Contexts

module _ where

  Function : Pred Intf 0ℓ
  Function =
    ⋃[ (fty@(n ∶ as ⟶ b)) ∶ FunTy ]
      ( Up (Just (fun fty))
      ✴ Down (Body as b)
      )

  pattern function sig decl σ body = sig , decl ∙⟨ σ ⟩ ↓ body

  Program : Set
  Program = Down⁻ (
      ( Down (Just ((fun ("main" ∶ [] ⟶ void)))) -- reference to the main function
      ✴ Bigstar Function
      ) ⇑) builtins

  pattern program main σ fs globals = (↓ main ∙⟨ σ ⟩ fs) ⇈ globals
