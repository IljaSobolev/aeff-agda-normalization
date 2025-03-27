open import Data.Maybe
open import Data.Product hiding (Σ)

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

open import Types

module AEff where

-- ARITY ASSIGNMENT TO SIGNATURES OF SIGNALS, INTERRUPTS, AND BASE CONSTANTS

postulate Σₛ : Set                 -- signal and interrupt names

-- signal and interrupt names have decidable equality
postulate decₛ : (op op' : Σₛ) → Dec (op ≡ op')

postulate payload : Σₛ → GType     -- payload type assignment for signal and interrupt names

postulate Σ-base : Set             -- set of base constants
postulate ar-base : Σ-base → BType -- arity assignment to base constants


-- SNOC LISTS FOR MODELLING CONTEXTS

infixl 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A


-- CONTEXTS AND VARIABLES IN THEM (I.E., DE BRUIJN INDICES)

Ctx = SnocList Type

data _∈_ (X : Type) : Ctx → Set where
  Hd : {Γ : Ctx} → X ∈ (Γ ∷ X)
  Tl : {Γ : Ctx} {Y : Type} → X ∈ Γ → X ∈ (Γ ∷ Y)


-- DERIVATIONS OF WELL-TYPED TERMS

mutual

  data _⊢V⦂_ (Γ : Ctx) : Type → Set where
  
    `_  : {X : Type} →
          X ∈ Γ →
          -------------
          Γ ⊢V⦂ X
          
    ``_  : (c : Σ-base) →
          --------------
          Γ ⊢V⦂ ``(ar-base c)
          
    ƛ   : {X : Type}
          {C : Type} →
          Γ ∷ X ⊢M⦂ C → 
          -------------
          Γ ⊢V⦂ X ⇒ C

    ⟨_⟩ : {X : Type} →
          Γ ⊢V⦂ X →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩

    -- a default value of promise type, representing a promise that would never be fulfilled
    -- helps with normalisation proof

    ★   : {X : Type} →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩
          
          
  infix 40 _·_

  data _⊢M⦂_ (Γ : Ctx) : Type → Set where

    return          : {X : Type} →
                      Γ ⊢V⦂ X →
                      -----------------
                      Γ ⊢M⦂ X

    let=_`in_       : {X Y : Type} →
                      Γ ⊢M⦂ X →
                      Γ ∷ X ⊢M⦂ Y →
                      -----------------------
                      Γ ⊢M⦂ Y

    _·_             : {X : Type}
                      {C : Type} → 
                      Γ ⊢V⦂ X ⇒ C →
                      Γ ⊢V⦂ X →
                      -------------
                      Γ ⊢M⦂ C

    ↑               : {X : Type}
                      (op : Σₛ) →
                      Γ ⊢V⦂ ``(payload op) →
                      Γ ⊢M⦂ X →
                      ----------------------
                      Γ ⊢M⦂ X

    ↓               : {X : Type}
                      (op : Σₛ) →
                      Γ ⊢V⦂ ``(payload op) →
                      Γ ⊢M⦂ X →
                      ----------------------
                      Γ ⊢M⦂ X

    promise_↦_`in_ : {X Y : Type}
                       (op : Σₛ) →
                       Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ →
                       Γ ∷ ⟨ X ⟩ ⊢M⦂ Y →
                       ------------------------------------------
                       Γ ⊢M⦂ Y

    await_until_    : {X : Type}
                      {C : Type} → 
                      Γ ⊢V⦂ ⟨ X ⟩ →
                      Γ ∷ X ⊢M⦂ C →
                      --------------
                      Γ ⊢M⦂ C


-- DERIVATIONS OF WELL-TYPED PROCESSES

infix 10 _⊢P⦂_

data _⊢P⦂_ (Γ : Ctx) : PType → Set where

  run     : {X : Type} →
            Γ ⊢M⦂ X →
            -------------------
            Γ ⊢P⦂ ``` X

  _∥_     : {PP : PType}
            {QQ : PType} →
            Γ ⊢P⦂ PP →
            Γ ⊢P⦂ QQ →
            --------------
            Γ ⊢P⦂ (PP ∥ QQ)

  ↑       : {PP : PType}
            (op : Σₛ) →
            Γ ⊢V⦂ ``(payload op) →
            Γ ⊢P⦂ PP →
            ----------------------
            Γ ⊢P⦂ PP

  ↓       : {PP : PType}
            (op : Σₛ) →
            Γ ⊢V⦂ ``(payload op) →
            Γ ⊢P⦂ PP →
            ----------------------
            Γ ⊢P⦂ PP
