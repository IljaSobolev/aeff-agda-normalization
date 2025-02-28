open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Data.Sum

open import AEff
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module AwaitingComputations where

-- COMPUTATIONS THAT ARE TEMPORARILY STUCK DUE TO AWAITING FOR A PARTICULAR PROMISE
    
data _⧗_ {Γ : Ctx} {X : Type} (x : ⟨ X ⟩ ∈ Γ) : {C : Type} → Γ ⊢M⦂ C → Set where

  await     : {C : Type}
              {M : Γ ∷ X ⊢M⦂ C} →
              -------------------------
              x ⧗ (await (` x) until M)

  let-in    : {X Y : Type}
              {M : Γ ⊢M⦂ X}
              {N : Γ ∷ X ⊢M⦂ Y} →
              x ⧗ M →
              -----------------------------
              x ⧗ (let= M `in N)

  interrupt : {X : Type}
              {op : Σₛ}
              {V : Γ ⊢V⦂ ``(payload op)}
              {M : Γ ⊢M⦂ X} →
              x ⧗ M →
              -------------------------
              x ⧗ (↓ op V M)