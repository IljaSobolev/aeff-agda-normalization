open import AEffBaseSN.AEffBase.Types

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload; Σ-base; ar-base)

module AEffBaseSN.AEffBase.AEff where

variable
  op op' : Σₛ

-- SNOC LISTS FOR MODELLING CONTEXTS

infixl 30 _∷_
data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A


-- CONTEXTS AND VARIABLES IN THEM (I.E., DE BRUIJN INDICES)

Ctx = SnocList Type

variable
  Γ Γ' Γ'' Δ Δ' : Ctx

infix 4 _∈_
data _∈_ (X : Type) : Ctx → Set where
  Hd : X ∈ Γ ∷ X
  Tl : X ∈ Γ → X ∈ Γ ∷ Y


-- DERIVATIONS OF WELL-TYPED TERMS

data _⊢V⦂_ (Γ : Ctx) : Type → Set

data _⊢M⦂_ (Γ : Ctx) (Y : Type) : Set

data _⊢V⦂_ Γ where
  `_  : X ∈ Γ → Γ ⊢V⦂ X
  ``_ : (c : Σ-base) → Γ ⊢V⦂ ```(ar-base c)
  ƛ   : Γ ∷ X ⊢M⦂ Y → Γ ⊢V⦂ X ⇒ Y
  ⟨_⟩ : Γ ⊢V⦂ X → Γ ⊢V⦂ ⟨ X ⟩

infix 40 _·_
data _⊢M⦂_ Γ Y where

  return         : Γ ⊢V⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  _·_            : Γ ⊢V⦂ X ⇒ Y →
                   Γ ⊢V⦂ X →
                   -------
                   Γ ⊢M⦂ Y

  let=_`in_      : Γ ⊢M⦂ X →
                   Γ ∷ X ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  ↑              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  ↓              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  promise_↦_`in_ : (op : Σₛ) →
                   Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ →
                   Γ ∷ ⟨ X ⟩ ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  await_until_   : Γ ⊢V⦂ ⟨ X ⟩ →
                   Γ ∷ X ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

variable
  V V' W W' : Γ ⊢V⦂ X
  M M' N N' L L' : Γ ⊢M⦂ X


-- DERIVATIONS OF WELL-TYPED PROCESSES

infix 10 _⊢P⦂_
data _⊢P⦂_ (Γ : Ctx) : PType → Set where

  run : Γ ⊢M⦂ X →
        ------------
        Γ ⊢P⦂ ```` X

  _∥_ : Γ ⊢P⦂ PP →
        Γ ⊢P⦂ QQ →
        -------------
        Γ ⊢P⦂ PP ∥ QQ

  ↑   : (op : Σₛ) →
        Γ ⊢V⦂ ```(payload op) →
        Γ ⊢P⦂ PP →
        --------
        Γ ⊢P⦂ PP

  ↓   : (op : Σₛ) →
        Γ ⊢V⦂ ```(payload op) →
        Γ ⊢P⦂ PP →
        --------
        Γ ⊢P⦂ PP

variable
  P P' Q Q' R R' : Γ ⊢P⦂ PP