module JVM.Defaults.Transform.Contextualize where

open import Data.Product
open import Relation.Ternary.Data.ReflexiveTransitive

open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import JVM.Types
open import JVM.Model StackTy

open import JVM.Defaults.Syntax.Contextual.Interface StackTy
open import JVM.Defaults.Syntax.Instructions as Src
open import JVM.Defaults.Syntax.Contextual.Instructions as Tgt


module _ Γ where
  open import JVM.Defaults.Transform.Contextualize.Monad StackTy Tgt.⟨ Γ ∣_↝_⟩ public
    using (Contextualizer)

module _ {Γ} where
  open import JVM.Defaults.Transform.Contextualize.Monad StackTy Tgt.⟨ Γ ∣_↝_⟩ public
    using (end)

transform : ∀ {τ₁ τ₂ : StackTy} {Γ K} → Src.⟪ Γ ∣ τ₁ ↝ τ₂ ⟫ K → Contextualizer Γ τ₁ τ₂ K
transform nil      = end
transform (cons (instr i   Rel₃.∙⟨ σ ⟩ b)) = {!!}
transform (cons (labeled i Rel₃.∙⟨ σ ⟩ b)) = {!!}
