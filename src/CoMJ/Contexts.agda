module CoMJ.Contexts c where

open import MJ.Types c
open import MJ.LexicalScope c

open import Level
open import Algebra
open import Function
open import Data.Product as P
open import Data.List
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Membership.Propositional
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality as PEq
open import Relation.Ternary.Separation

{- Splitting All over separation -}
module _ where

  parts : ∀ {p} {P : Pred Ty p} → Γ₁ ⊎ Γ₂ ≣ Γ → All P Γ → All P Γ₁ × All P Γ₂
  parts [] [] = [] , []
  parts (duplicate σ) (px ∷ pxs) with parts σ pxs
  ... | l , r = px ∷ l , px ∷ r
  parts (consˡ σ) (px ∷ pxs) with parts σ pxs
  ... | l , r = px ∷ l , r
  parts (consʳ σ) (px ∷ pxs) with parts σ pxs
  ... | l , r = l , px ∷ r

{- Effect annotations -}
module _ where

  record IsEffect (𝑭 : Ty → Set) : Set where
    field
      _∙_         : ∀[ 𝑭 ⇒ 𝑭 ⇒ 𝑭 ]
      isSemigroup : ∀ a → IsCommutativeSemigroup _≡_ (_∙_ {a})

    module _ {a} where
      open IsCommutativeSemigroup (isSemigroup a) public

  record Effect : Set₁ where
    constructor effect
    field
      {𝑭}      : Ty → Set
      isEffect : IsEffect 𝑭

    open IsEffect isEffect public

    -- a column first representation of effect annotations on contexts
    Annot : Ctx → Set
    Annot Γ = All 𝑭 Γ

  open Effect public

  record Effects : Set₁ where
    field
      effects : List Effect

    Annots : Ctx → Set₁
    Annots Γ = All (λ ef → Effect.Annot ef Γ) effects

    Carrier = Σ[ Γ ∈ Ctx ] Annots Γ

    _through_ : ∀ {p} → Annots Γ → Pred Carrier p → Set p
    φ through P = P (-, φ)

    HasEffect : Effect → Set₁
    HasEffect ef = ef ∈ effects

    _%[_] : ∀ {Γ E} → Annots Γ → HasEffect E → Annot E Γ
    φ %[ 𝑭 ] = All.lookup φ 𝑭

    _%[_]=_ : ∀ {Γ E} → Annots Γ → HasEffect E → Annot E Γ → Annots Γ
    φ %[ 𝑭 ]= f = φ All.[ 𝑭 ]≔ f

    _≺_ : Annots Γ → Γ₁ ⊎ Γ₂ ≣ Γ → Annots Γ₁ × Annots Γ₂
    φ ≺ σ
      = All.map (proj₁ ∘ parts σ) φ
      , All.map (proj₂ ∘ parts σ) φ

    record _⇑⟨_⟩_ {p q} {Γₗ Γᵣ Γ : Ctx}
      (P : Pred Carrier p)
      (σ : Γₗ ⊎ Γᵣ ≣ Γ)
      (Q : Pred Carrier q)
      (φ : Annots Γ) : Set (p ⊔ q) where
      open Σ (φ ≺ σ) renaming (proj₁ to φₗ; proj₂ to φᵣ)
      field
        px : φₗ through P
        qx : φᵣ through Q

{- Merging annotations along context splits using the effect's operation -}
module _ (eff : Effect) where
  module F = Effect eff

  merge : Γ₁ ⊎ Γ₂ ≣ Γ → F.Annot Γ₁ → F.Annot Γ₂ → F.Annot Γ
  merge (duplicate σ)  (m ∷ m₁) (n ∷ m₂) = (m F.∙ n) ∷ (merge σ m₁ m₂)
  merge (consˡ σ)      (m ∷ m₁) m₂       = m ∷ (merge σ m₁ m₂)
  merge (consʳ σ)      m₁       (m ∷ m₂) = m ∷ (merge σ m₁ m₂)
  merge []             _        _        = []

  merge-comm : ∀ (σ : Γ₁ ⊎ Γ₂ ≣ Γ) {m₁ m₂} → merge σ m₁ m₂ ≡ merge (⊎-comm σ) m₂ m₁
  merge-comm (duplicate σ) {m ∷ m₁} {n ∷ m₂} = cong₂ _∷_ (F.comm m n) (merge-comm σ)
  merge-comm (consˡ σ)     {m ∷ m₁} {m₂}     = cong (_ ∷_) (merge-comm σ)
  merge-comm (consʳ σ)     {m₁}     {n ∷ m₂} = cong (_ ∷_) (merge-comm σ)
  merge-comm []                              = _≡_.refl

  merge-assoc : ∀ (σ₁ : Γ₁ ⊎ Γ₂ ≣ Γ₃) (σ₂ : Γ₃ ⊎ Γ₄ ≣ Γ) {m₁}{m₂}{m₃} →
    let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in
    merge σ₂ (merge σ₁ m₁ m₂) m₃ ≡ merge σ₃ m₁ (merge σ₄ m₂ m₃)

  merge-assoc σ₁ (consʳ σ₂) {_} {_} {n ∷ m₃} =
    cong (_ ∷_) (merge-assoc σ₁ σ₂)

  merge-assoc (duplicate σ₁) (duplicate σ₂) {_ ∷ _} {_ ∷ _} {_ ∷ _} =
    cong₂ _∷_ (F.assoc _ _ _) (merge-assoc σ₁ σ₂)

  merge-assoc (consˡ σ₁) (duplicate σ₂) {_ ∷ _} {_} {_ ∷ _} =
    cong (_ ∷_) (merge-assoc σ₁ σ₂)
  merge-assoc (consʳ σ₁) (duplicate σ₂) {_} {_ ∷ _} {_ ∷ _} =
    cong (_ ∷_) (merge-assoc σ₁ σ₂)

  merge-assoc (duplicate σ₁) (consˡ σ₂) {_ ∷ _} {_ ∷ _} {_} =
    cong (_ ∷_) (merge-assoc σ₁ σ₂)
  merge-assoc (consˡ σ₁) (consˡ σ₂) {_ ∷ _} {_} {_} =
    cong (_ ∷_) (merge-assoc σ₁ σ₂)
  merge-assoc (consʳ σ₁) (consˡ σ₂) {_} {_ ∷ _} {_} =
    cong (_ ∷_) (merge-assoc σ₁ σ₂)

  merge-assoc [] [] = PEq.refl

  merge-idˡ : ∀ {Γ} {F : F.Annot Γ} σ → merge σ [] F ≡ F
  merge-idˡ {[]}    {[]}    []        = PEq.refl
  merge-idˡ {_ ∷ _} {_ ∷ _} (consʳ σ) = cong (_ ∷_) (merge-idˡ σ)

{- Separation on annotated contexts -}
module Instances (efs : Effects) where

  open Effects efs
    
  _∙_≣_ : Carrier → Carrier → Carrier → Set _
  (Γ₁ , M₁) ∙ (Γ₂ , M₂) ≣ (Γ , M) =
    Σ[ σ ∈ Γ₁ ⊎ Γ₂ ≣ Γ ]
      ∀ {ef} (m : HasEffect ef) →
        merge ef σ
          (All.lookup M₁ m)
          (All.lookup M₂ m)
          ≡ All.lookup M m

  instance eff-raw : RawSep Carrier
  RawSep._⊎_≣_ eff-raw = _∙_≣_

  postulate instance eff-sep : IsSep eff-raw
  -- IsSep.⊎-comm eff-sep  (σ , eqs) =
  --   -, λ {ef} m → trans (sym (merge-comm _ σ)) (eqs m)
  -- IsSep.⊎-assoc eff-sep (σ₁ , eqs₁) (σ₂ , eqs₂) =
  --   -, (-, λ {ef} m → trans (sym {!!}) (eqs₂ m)) , (-, λ {ef} m → refl)

  {- TODO add to stdlib -}
  module _ {a p} {A : Set a} {P : Pred A p} where
    open import Data.List.Relation.Unary.Any
    lookup-tabulate : ∀  {xs : List A} {f : ∀ {x} → x ∈ xs → P x} →
      ∀ {x} (m : x ∈ xs) → All.lookup (All.tabulate f) m ≡ f m
    lookup-tabulate (here refl) = PEq.refl
    lookup-tabulate (there m)   = lookup-tabulate m

    {- Extensional equality for All -}
    all-ext : ∀ {xs : List A} {pxs qxs : All P xs}
      → (∀ {x} (m : x ∈ xs) → All.lookup pxs m ≡ All.lookup qxs m)
      → pxs ≡ qxs
    all-ext {_} {[]}       {[]}       eqs = PEq.refl
    all-ext {_} {px ∷ pxs} {qx ∷ qxs} eqs =
      cong₂ _∷_
        (eqs (here PEq.refl))
        (all-ext (λ m → eqs (there m)))

  annots-zero : Annots ε
  annots-zero = All.tabulate λ _ → []

  instance eff-unit⁺ : HasUnit⁺ eff-raw (ε , annots-zero)
  HasUnit⁺.⊎-idˡ eff-unit⁺ {_ , Φ} = ⊎-idˡ , λ m → (begin
    merge _ ⊎-idˡ (All.lookup annots-zero m) (All.lookup Φ m)
      ≡⟨ cong (λ l → merge _ ⊎-idˡ l (All.lookup Φ m)) (lookup-tabulate m) ⟩
    merge _ ⊎-idˡ [] (All.lookup Φ m)
      ≡⟨ merge-idˡ _ ⊎-idˡ ⟩
    All.lookup Φ m ∎)
      where open ≡-Reasoning

  postulate instance eff-unit⁻ : HasUnit⁻ eff-raw (ε , annots-zero)
  -- HasUnit⁻.⊎-id⁻ˡ eff-unit⁻ {_ , _} (fst , eqs) with ⊎-id⁻ˡ fst
  -- ... | refl = cong (_ ,_) (all-ext λ m → {!!})

{- Constructing a commutative semigroup on a product using prop equality -}
{- TODO add to stdlib? -}
module _ {a b} {A : Set a} {B : Set b}
  {_∙ₗ_ : A → A → A} (sgₗ : IsCommutativeSemigroup _≡_ _∙ₗ_)
  {_∙ᵣ_ : B → B → B} (sgᵣ : IsCommutativeSemigroup _≡_ _∙ᵣ_)
  where

  op = P.zip _∙ₗ_ _∙ᵣ_

  _×-isMagma_ : IsMagma _≡_ op
  IsMagma.isEquivalence _×-isMagma_ = PEq.isEquivalence
  IsMagma.∙-cong _×-isMagma_ PEq.refl PEq.refl = PEq.refl

  _×-isSemigroup_ : IsSemigroup _≡_ op
  IsSemigroup.isMagma _×-isSemigroup_ = _×-isMagma_
  IsSemigroup.assoc _×-isSemigroup_ x y z =
    cong₂ _,_
      (IsCommutativeSemigroup.assoc sgₗ _ _ _)
      (IsCommutativeSemigroup.assoc sgᵣ _ _ _)

  _×-isCommutativeSemigroup_ : IsCommutativeSemigroup _≡_ op
  IsCommutativeSemigroup.isSemigroup _×-isCommutativeSemigroup_ = _×-isSemigroup_
  IsCommutativeSemigroup.comm _×-isCommutativeSemigroup_ x y =
    cong₂ _,_
      (IsCommutativeSemigroup.comm sgₗ _ _)
      (IsCommutativeSemigroup.comm sgᵣ _ _)

{- We describe dataflow using two effects using the same carrier, but different operations -}
module Dataflow
  (effects : Effects)
  {𝑭   : Ty → Set}
  {eff₁} (requires : Effects.HasEffect effects (effect {𝑭} eff₁))
  {eff₂} (ensures  : Effects.HasEffect effects (effect {𝑭} eff₂))
  where
  open Effects effects hiding (effects)

  {- Parallel composition is just the star -}
  open Instances effects
  open RawSep eff-raw using ()
    renaming (_✴_ to _∥_) public
  open IsSep eff-sep using ()
    renaming (✴-swap to ∥-comm; ✴-assocₗ to ∥-assocₗ; ✴-assocᵣ to ∥-assocᵣ)
    public
  open HasUnit⁺ eff-unit⁺ using ()
    renaming (✴-idˡ to ∥-idˡ; ✴-idʳ to ∥-idʳ)
    public
  open HasUnit⁻ eff-unit⁻ using ()
    renaming (✴-id⁻ˡ to ∥-id⁻ˡ; ✴-id⁻ʳ to ∥-id⁻ʳ)
    public

  {- The identity flow (Usually you want Emp instead!) -}
  𝑰 : ∀ {Γ} → Annots Γ → Set
  𝑰 φ = φ %[ requires ] ≡ φ %[ ensures ]

  record _▹_ {p q} (P : Pred Carrier p) (Q : Pred Carrier q) (c : Carrier) : Set (p ⊔ q) where
    constructor seq
    open Σ c renaming (proj₁ to Γ'; proj₂ to φ)
    field
      -- the context splitting
      {Γₗ Γᵣ} : Ctx
      sep : Γₗ ⊎ Γᵣ ≣ Γ'

      -- {φᵢ} : All 𝑭 Γ'
      -- px : Bridge         sep  P (φ %[ ensures ]= φᵢ)
      -- qx : Bridge (⊎-comm sep) Q (φ %[ requires ]= φᵢ)
  
  -- ▹-id⁻ˡ : ∀ {p} {P : Pred Carrier p} → ∀[ Emp ▹ P ⇒ P ]
  -- ▹-id⁻ˡ (seq σ px qx) = {!!}

-- {- For now we annotate our contexts with the effect annotation "being initialized" (i.e., being readable) -}
-- module _ where
--   open import Data.Bool
--     using ()
--     renaming (Bool to Mode; true to rw; false to w; _∧_ to _⊔ₘ_; _∨_ to _⊓ₘ_)
--     public

--   open import Data.Bool.Properties using (∨-isCommutativeMonoid; ∧-isCommutativeMonoid)
--   open IsCommutativeMonoid

--   Modes = Mode × Mode

--   Moding : Ctx → Set
--   Moding = All (const Modes)

--   ModedCtx : Set
--   ModedCtx = Σ Ctx Moding

--   open Effects
--     (isCommutativeSemigroup ∨-isCommutativeMonoid)
--     (isCommutativeSemigroup ∧-isCommutativeMonoid)
