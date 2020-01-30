{- A co-de-bruijn encoding of MJ values -}
import MJ.Classtable.Core as Core

module JVM.Defaults.Syntax.Values {c}(Ct : Core.Classtable c) where

open import JVM.Prelude hiding (Σ; _⊢_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open Core.Classtable Ct

open import MJ.Types c
open import JVM.Defaults.Syntax.Frames Ct

data Val : Ty → Pred World 0ℓ where
  null : ε[ Val (ref cid) ]
  unit : ε[ Val void ]
  num  : ℕ → ε[ Val int ] 
  ref  : cid <∶ pid → ∀[ Just (obj cid) ⇒ Val (ref pid) ]

data Const : Ty → Set where
  null : ∀ {c} → Const (ref c)
  num  : ℕ     → Const int

constvalue : Const a → ε[ Val a ] 
constvalue null    = null
constvalue (num x) = num x

-- record ObjEncoding : Set (lsuc lzero) where
--   field
--     Obj : World c → Cid c → Set
--     weaken-obj : ∀ {W W'} cid → W' ⊒ W → Obj W cid → Obj W' cid
--     getter : ∀ {W m a} c → Obj W c → IsMember c FIELD m a → Val W a
--     setter : ∀ {W m a} c → Obj W c → IsMember c FIELD m a → Val W a → Obj W c
--     defaultObject : ∀ {W} c → Obj W c

data StoreVal : Ty⁺ → Pred World 0ℓ where
  val : ∀[ Val a ⇒ StoreVal (vty a) ]
  -- obj : ∀ cid → Obj W cid → StoreVal W (obj cid)
