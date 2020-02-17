open import Data.Maybe
open import Data.Product hiding (Σ)

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

open import EffectAnnotations
open import Types

module Calculus where

-- ARITY ASSIGNMENT TO SIGNATURES OF SIGNALS, INTERRUPTS, AND BASE CONSTANTS

postulate arₙ : Σₙ → GType -- arity assignment for signal names

postulate Σ-base : Set             -- set of base constants
postulate ar-base : Σ-base → BType -- arity assignment to base constants


-- SNOC LISTS FOR MODELLING CONTEXTS

infixl 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A


append : {A : Set} → SnocList A → SnocList A → SnocList A
append l [] = l
append l (l' ∷ a) = (append l l') ∷ a


append-assoc : {A : Set} →
               (l l' l'' : SnocList A) →
               ---------------------------------------------------
               append l (append l' l'') ≡ append (append l l') l''

append-assoc l l' [] =
  refl
append-assoc l l' (l'' ∷ a) =
  cong (λ l''' → l''' ∷ a) (append-assoc l l' l'')


append-lunit : {A : Set} →
               {l : SnocList A} →
               ------------------
               l ≡ append [] l 

append-lunit {_} {[]} =
  refl
append-lunit {_} {(l ∷ a)} =
  cong (λ l' → l' ∷ a) append-lunit


-- CONTEXTS AND VARIABLES IN THEM (I.E., DE BRUIJN INDICES)

Ctx = SnocList VType

data _∈_ (X : VType) : Ctx → Set where
  Hd : {Γ : Ctx} → X ∈ (Γ ∷ X)
  Tl : {Γ : Ctx} {Y : VType} → X ∈ Γ → X ∈ (Γ ∷ Y)


-- DECIDING EQUALITY OF VARIABLES

dec-var : {X : VType} {Γ : Ctx} → (x y : X ∈ Γ) → Dec (x ≡ y)
dec-var Hd Hd =
  yes refl
dec-var Hd (Tl y) =
  no (λ ())
dec-var (Tl x) Hd =
  no (λ ())
dec-var (Tl x) (Tl y) with dec-var x y
dec-var (Tl x) (Tl .x) | yes refl =
  yes refl
dec-var {X} (Tl x) (Tl y) | no ¬p =
  no (λ { refl → contradiction refl ¬p })


-- DERIVATIONS OF WELL-TYPED TERMS

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where
  
    `_  : {X : VType} →
          X ∈ Γ →
          -------------
          Γ ⊢V⦂ X
          
    ``_  : (c : Σ-base) →
          --------------
          Γ ⊢V⦂ ``(ar-base c)
          
    ƛ   : {X : VType}
          {C : CType} →
          Γ ∷ X ⊢M⦂ C → 
          -------------
          Γ ⊢V⦂ X ⇒ C

    ⟨_⟩ : {X : VType} →
          Γ ⊢V⦂ X →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩
          
  infix 40 _·_

  data _⊢M⦂_ (Γ : Ctx) : CType → Set where

    return           : {X : VType}
                       {o : O}
                       {i : I} →
                       Γ ⊢V⦂ X →
                       -----------------
                       Γ ⊢M⦂ X ! (o , i)

    let=_`in_        : {X Y : VType}
                       {o : O}
                       {i : I} → 
                       Γ ⊢M⦂ X ! (o , i) →
                       Γ ∷ X ⊢M⦂ Y ! (o , i) →
                       -----------------------
                       Γ ⊢M⦂ Y ! (o , i)

    _·_              : {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ X ⇒ C →
                       Γ ⊢V⦂ X →
                       -------------
                       Γ ⊢M⦂ C

    ↑                : {X : VType}
                       {o : O}
                       {i : I} →
                       (op : Σₙ) →
                       op ∈ₒ o →
                       Γ ⊢V⦂ ``(arₙ op) →
                       Γ ⊢M⦂ X ! (o , i) →
                       -------------------
                       Γ ⊢M⦂ X ! (o , i)

    ↓                : {X : VType}
                       {o : O}
                       {i : I}
                       (op : Σₙ) →
                       Γ ⊢V⦂ ``(arₙ op) →
                       Γ ⊢M⦂ X ! (o , i) →
                       ----------------------
                       Γ ⊢M⦂ X ! op ↓ₑ (o , i)

    promise_∣_↦_`in_ : {X Y : VType}
                       {o o' : O}
                       {i i' : I} → 
                       (op : Σₙ) →
                       lkpᵢ op i ≡ just (o' , i') →
                       Γ ∷ ``(arₙ op) ⊢M⦂ X ! (o' , i') →
                       Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i) →
                       ----------------------------------
                       Γ ⊢M⦂ Y ! (o , i)

    await_until_     : {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ ⟨ X ⟩ →
                       Γ ∷ X ⊢M⦂ C →
                       --------------
                       Γ ⊢M⦂ C

    subsume          : {X : VType}
                       {o o' : O}
                       {i i' : I} →
                       o ⊑ₒ o' →
                       i ⊑ᵢ i' → 
                       Γ ⊢M⦂ X ! (o , i) →
                       -------------------
                       Γ ⊢M⦂ X ! (o' , i')
                        
