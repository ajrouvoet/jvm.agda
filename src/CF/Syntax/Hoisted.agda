module CF.Syntax.Hoisted where

open import Level
open import Data.List

open import Relation.Unary hiding (_⊢_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

open import CF.Types
open import CF.Contexts
open import CF.Syntax using (module Statements)
open import CF.Syntax using (Exp) public

mutual
  Stmt = Statements.Statement Block

  {- This is Bigstar, but Agda cannot termination check that -}
  data Block (r : Ty) : Pred Ctx 0ℓ where
    nil  : ε[ Block r ]
    cons : ∀[ Stmt r ✴ Block r ⇒ Block r ]

open import Relation.Unary.PredicateTransformer hiding (_⍮_)
open import Data.Product

-- make constructors visible
open Exp public
open Statements Block public
open import CF.Syntax.Programs (λ as b → Closed (as ⊢ ◇ (Block b))) public
open CoDeBruijn public
open import CF.Contexts using (_⊢_) public
