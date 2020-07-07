{-# OPTIONS --rewriting #-}
module CF.Contexts.Rewriting where

open import Data.List
open import Data.List.Properties

open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
open import CF.Types

++-assoc-← : ∀ (xs ys zs : List Ty) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc-← = λ x y z → sym (++-assoc x y z)

++-identityʳ-← : ∀ (xs : List Ty) → xs ++ [] ≡ xs
++-identityʳ-← xs = ++-identityʳ xs

{-# REWRITE ++-assoc-← #-}
{-# REWRITE ++-identityʳ-← #-}
