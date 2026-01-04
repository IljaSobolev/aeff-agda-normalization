{-# OPTIONS --guardedness #-}

open import Data.Maybe
open import Data.Product hiding (Σ)

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

open import AEffReinstSN.CoinductiveEffectAnnotations
open import AEffReinstSN.Types

module AEffReinstSN.AEff where

-- ARITY ASSIGNMENT TO SIGNATURES OF SIGNALS, INTERRUPTS, AND BASE CONSTANTS

postulate payload : Σₛ → GType     -- payload type assignment for signal and interrupt names

postulate Σ-base : Set             -- set of base constants
postulate ar-base : Σ-base → BType -- arity assignment to base constants


-- SNOC LISTS FOR MODELLING CONTEXTS

infixl 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A


-- CONTEXTS AND VARIABLES IN THEM (I.E., DE BRUIJN INDICES)

Ctx = SnocList VType

data _∈_ (X : VType) : Ctx → Set where
  Hd : {Γ : Ctx} → X ∈ (Γ ∷ X)
  Tl : {Γ : Ctx} {Y : VType} → X ∈ Γ → X ∈ (Γ ∷ Y)


-- DERIVATIONS OF WELL-TYPED TERMS

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where
  
    `_  : {X : VType} →
          X ∈ Γ →
          -------------
          Γ ⊢V⦂ X
          
    ``_  : (c : Σ-base) →
          --------------
          Γ ⊢V⦂ ```(ar-base c)
          
    ƛ   : {X : VType}
          {C : CType} →
          Γ ∷ X ⊢M⦂ C → 
          -------------
          Γ ⊢V⦂ X ⇒ C

    inl : {X Y : VType} →
          Γ ⊢V⦂ X →
          -----------
          Γ ⊢V⦂ X + Y

    inr : {X Y : VType} →
          Γ ⊢V⦂ Y →
          ----------
          Γ ⊢V⦂ X + Y

    ⟨_⟩ : {X : VType} →
          Γ ⊢V⦂ X →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩

    u   : Γ ⊢V⦂ 𝟙
          
  infix 40 _·_

  data _⊢M⦂_ (Γ : Ctx) : CType → Set where

    return             : {X : VType}
                         {o : O}
                         {i : I} →
                         Γ ⊢V⦂ X →
                         -----------------
                         Γ ⊢M⦂ X ! (o , i)

    let=_`in_          : {X Y : VType}
                         {o : O}
                         {i : I} → 
                         Γ ⊢M⦂ X ! (o , i) →
                         Γ ∷ X ⊢M⦂ Y ! (o , i) →
                         -----------------------
                         Γ ⊢M⦂ Y ! (o , i)

    _·_                : {X : VType}
                         {C : CType} → 
                         Γ ⊢V⦂ X ⇒ C →
                         Γ ⊢V⦂ X →
                         -------------
                         Γ ⊢M⦂ C

    ↑                  : {X : VType}
                         {o : O}
                         {i : I} →
                         (op : Σₛ) →
                         op ∈ₒ o →
                         Γ ⊢V⦂ ```(payload op) →
                         Γ ⊢M⦂ X ! (o , i) →
                         ----------------------
                         Γ ⊢M⦂ X ! (o , i)

    ↓                  : {X : VType}
                         {o : O}
                         {i : I}
                         (op : Σₛ) →
                         Γ ⊢V⦂ ```(payload op) →
                         Γ ⊢M⦂ X ! (o , i) →
                         ----------------------
                         Γ ⊢M⦂ X ! op ↓ₑ (o , i)

    promise_∣_,_↦_`in_ : {X Y : VType}
                         {o o' : O}
                         {i i' : I} → 
                         (op : Σₛ) →
                         just (o' , i') ⊑-aux imap i op →
                         (∅ᵢ [ op ↦ just (o' , i') ]ᵢ) ⊑ᵢ i' →
                         Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙 ! (o' , i') →
                         Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i) →
                         ------------------------------------------
                         Γ ⊢M⦂ Y ! (o , i)

    await_until_       : {X : VType}
                         {C : CType} → 
                         Γ ⊢V⦂ ⟨ X ⟩ →
                         Γ ∷ X ⊢M⦂ C →
                         --------------
                         Γ ⊢M⦂ C

    match+             : {X Y : VType}
                         {C : CType} →
                         Γ ⊢V⦂ X + Y →
                         Γ ∷ X ⊢M⦂ C →
                         Γ ∷ Y ⊢M⦂ C →
                         --------
                         Γ ⊢M⦂ C

    coerce             : {X : VType}
                         {o o' : O}
                         {i i' : I} →
                         o ⊑ₒ o' →
                         i ⊑ᵢ i' → 
                         Γ ⊢M⦂ X ! (o , i) →
                         -------------------
                         Γ ⊢M⦂ X ! (o' , i')
                        

-- DERIVATIONS OF WELL-TYPED PROCESSES

infix 10 _⊢P⦂_

data _⊢P⦂_ (Γ : Ctx) : {o : O} → PType o → Set where

  run     : {X : VType}
            {o : O}
            {i : I} →
            Γ ⊢M⦂ X ! (o , i) →
            -------------------
            Γ ⊢P⦂ X ‼ o , i

  _∥_     : {o o' : O}
            {PP : PType o} →
            {QQ : PType o'} → 
            Γ ⊢P⦂ PP →
            Γ ⊢P⦂ QQ →
            --------------
            Γ ⊢P⦂ (PP ∥ QQ)

  ↑       : {o : O} →
            {PP : PType o}
            (op : Σₛ) →
            op ∈ₒ o →
            Γ ⊢V⦂ ```(payload op) →
            Γ ⊢P⦂ PP →
            ----------------------
            Γ ⊢P⦂ PP

  ↓       : {o : O}
            {PP : PType o}
            (op : Σₛ) →
            Γ ⊢V⦂ ```(payload op) →
            Γ ⊢P⦂ PP →
            ----------------------
            Γ ⊢P⦂ op ↓ₚ PP