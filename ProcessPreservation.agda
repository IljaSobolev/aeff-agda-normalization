open import Data.List renaming (_∷_ to _∷ₗ_ ; [_] to [_]ₗ)
open import Data.Maybe
open import Data.Product
open import Data.Sum

open import AEff
open import Preservation
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module ProcessPreservation where


-- EVALUATION CONTEXTS FOR PROCESSES

infix 10 _⊢F⦂_

data _⊢F⦂_ (Γ : Ctx) : PType → Set where

  [-]     : {PP : PType} →
            --------------
            Γ ⊢F⦂ PP

  _∥ₗ_    : {PP : PType}
            {QQ : PType} → 
            Γ ⊢F⦂ PP →
            Γ ⊢P⦂ QQ →
            ------------------
            Γ ⊢F⦂ (PP ∥ QQ)

  _∥ᵣ_    : {PP : PType}
            {QQ : PType} →
            Γ ⊢P⦂ PP →
            Γ ⊢F⦂ QQ →
            ------------------
            Γ ⊢F⦂ (PP ∥ QQ)

  ↑       : {PP : PType}  →
            (op : Σₛ) →
            Γ ⊢V⦂ ``(payload op) →
            Γ ⊢F⦂ PP →
            ----------------------
            Γ ⊢F⦂ PP

  ↓       : {PP : PType}
            (op : Σₛ) →
            Γ ⊢V⦂ ``(payload op) →
            Γ ⊢F⦂ PP →
            ----------------------
            Γ ⊢F⦂ PP
            

-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED PROCESS EVALUATION CONTEXT

hole-ty-f : {Γ : Ctx} {PP : PType} → Γ ⊢F⦂ PP → PType
hole-ty-f {_} {PP} [-] =
  PP
hole-ty-f (_∥ₗ_ {PP} {QQ} F Q) =
  hole-ty-f F
hole-ty-f (_∥ᵣ_ {PP} {QQ} P F) =
  hole-ty-f F
hole-ty-f (↑ op V F) =
  hole-ty-f F
hole-ty-f (↓ op V F) =
  hole-ty-f F


-- FILLING A WELL-TYPED PROCESS EVALUATION CONTEXT

infix 30 _[_]f

_[_]f : {Γ : Ctx} {PP : PType} → (F : Γ ⊢F⦂ PP) → (P : Γ ⊢P⦂ (hole-ty-f F)) → Γ ⊢P⦂ PP
[-] [ P ]f =
  P
(F ∥ₗ Q) [ P ]f =
  (F [ P ]f) ∥ Q
(Q ∥ᵣ F) [ P ]f =
  Q ∥ (F [ P ]f)
(↑ op V F) [ P ]f =
  ↑ op V (F [ P ]f)
(↓ op V F) [ P ]f =
  ↓ op V (F [ P ]f)


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

{- THEOREM 4.7 -}

infix 10 _↝P_

data _↝P_ {Γ : Ctx} : {PP : PType} → Γ ⊢P⦂ PP → Γ ⊢P⦂ PP → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run     : {X : Type}
            {M N : Γ ⊢M⦂ X} → 
            M ↝ N →
            ---------------------------
            (run M) ↝P (run N)

  -- BROADCAST RULES

  ↑-∥ₗ    : {PP : PType}
            {QQ : PType}
            {op : Σₛ} → 
            (V : Γ ⊢V⦂ `` (payload op)) →
            (P : Γ ⊢P⦂ PP) →
            (Q : Γ ⊢P⦂ QQ) →
            ------------------------------------------
            ((↑ op V P) ∥ Q)
            ↝P
            ↑ op V (P ∥ ↓ op V Q)

  ↑-∥ᵣ    : {PP : PType}
            {QQ : PType}
            {op : Σₛ} → 
            (V : Γ ⊢V⦂ `` (payload op)) →
            (P : Γ ⊢P⦂ PP) →
            (Q : Γ ⊢P⦂ QQ) →
            ------------------------------------------
            (P ∥ (↑ op V Q))
            ↝P
            ↑ op V (↓ op V P ∥ Q)

  -- INTERRUPT PROPAGATION RULES

  ↓-run   : {X : Type}
            {op : Σₛ} → 
            (V : Γ ⊢V⦂ `` (payload op)) → 
            (M : Γ ⊢M⦂ X) →
            -----------------------------
            ↓ op V (run M)
            ↝P
            run (↓ op V M)

  ↓-∥     : {PP : PType}
            {QQ : PType}
            {op : Σₛ}
            (V : Γ ⊢V⦂ `` (payload op)) →
            (P : Γ ⊢P⦂ PP) →
            (Q : Γ ⊢P⦂ QQ) →
            -----------------------------
            ↓ op V (P ∥ Q)
            ↝P
            ((↓ op V P) ∥ (↓ op V Q))

  ↓-↑     : {PP : PType}
            {op : Σₛ}
            {op' : Σₛ} →
            (V : Γ ⊢V⦂ ``(payload op)) →
            (W : Γ ⊢V⦂ ``(payload op')) →
            (P : Γ ⊢P⦂ PP) →
            -----------------------------------
            ↓ op V (↑ op' W P)
            ↝P
            ↑ op' W (↓ op V P)

  -- SIGNAL HOISTING RULE

  ↑       : {X : Type}
            {op : Σₛ} → 
            (V : Γ ⊢V⦂ `` (payload op)) →
            (M : Γ ⊢M⦂ X) →
            -----------------------------
            run (↑ op V M)
            ↝P
            ↑ op V (run M)

  -- EVALUATION CONTEXT RULE

  context : {PP : PType}
            (F : Γ ⊢F⦂ PP)
            {P : Γ ⊢P⦂ (hole-ty-f F)}
            {Q : Γ ⊢P⦂ (hole-ty-f F)} →
            P ↝P Q →
            -----------------------------------------------------------------------------
            F [ P ]f
            ↝P
            F [ Q ]f