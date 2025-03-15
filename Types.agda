open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module Types where

-- BASE AND GROUND TYPES

postulate BType : Set -- set of base types

postulate dec-bty : (B B' : BType) → Dec (B ≡ B')

GType = BType


-- VALUE AND COMPUTATION TYPES

mutual

  data Type : Set where
    ``  : GType → Type
    _⇒_ : Type → Type → Type
    ⟨_⟩ : Type → Type

infix 30 _⇒_


-- PROCESS TYPES

data PType : Set where

  ```_ : (X : Type) →
        ---------------
        PType
  
  _∥_ : (PP : PType) →
        (QQ : PType) →
        ---------------------------
        PType
