open import AEff.Types using (BType; GType)

module AEffBaseSN.AEffBase.Types where

variable
  A : BType

-- VALUE AND COMPUTATION TYPES

infix 30 _⇒_
data Type : Set where
  ```  : GType → Type
  _⇒_  : Type → Type → Type
  ⟨_⟩  : Type → Type

variable
  X Y Z U : Type


-- PROCESS TYPES

data PType : Set where
  ````_ : Type → PType
  _∥_   : PType → PType → PType

variable
  PP QQ RR : PType