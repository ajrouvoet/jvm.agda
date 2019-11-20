import MJ.Classtable.Core as Core

module JVM.Compile {c} (Ct : Core.Classtable c) where

open import Relation.Unary
open import Relation.Ternary.Separation
open import Data.Product using (_,_)
open import Data.Bool
open import Data.List

open import MJ.Types c
open import MJ.LexicalScope c

open import JVM.Syntax.Hoisted Ct
open import JVM.Syntax.Frames Ct
open import JVM.Syntax.Bytecode Ct

-- For the moment we assume that all variables in the context are initialized.
-- This assumption is satisfied by store'ing defaults at the entry of a method.

initialize : Ctx → List RegTy
initialize = map (_, true)

mutual
  compile-block : Block r Γ →
                  let locals = initialize Γ in
                  ε[ ⟪ locals ∣ ψ ⇒ locals ∣ ψ ⟫ ]
  compile-block emp                     = block
  compile-block (cons (st ×⟨ σ ⟩ bl))   =
    let
      c₁ = compile-stmt  st 
      c₂ = compile-block bl
    in seq {!c₁!} $⟨ {!!} ⟩ {!!}

  compile-stmt  : Stmt r Γ →
                  let locals = initialize Γ in
                  ε[ ⟪ locals ∣ ψ ⇒ locals ∣ ψ ⟫ ]
  compile-stmt s = {!!}
