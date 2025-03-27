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
    
data _⧗_ {Γ : Ctx} {X : Type} : (x : Γ ⊢V⦂ ⟨ X ⟩) → {C : Type} → Γ ⊢M⦂ C → Set where

  await     : {C : Type}
              {M : Γ ∷ X ⊢M⦂ C}
              {x∈ : ⟨ X ⟩ ∈ Γ} →
              -------------------------------
              (` x∈) ⧗ (await (` x∈) until M)

  blocked   : {C : Type}
              {M : Γ ∷ X ⊢M⦂ C} →
              ---------------------
              ★ ⧗ (await ★ until M)

  let-in    : {Y Z : Type}
              {M : Γ ⊢M⦂ Y}
              {N : Γ ∷ Y ⊢M⦂ Z}
              {x : Γ ⊢V⦂ ⟨ X ⟩} →
              x ⧗ M →
              -----------------------------
              x ⧗ (let= M `in N)

  interrupt : {Y : Type}
              {op : Σₛ}
              {V : Γ ⊢V⦂ ``(payload op)}
              {M : Γ ⊢M⦂ Y}
              {x : Γ ⊢V⦂ ⟨ X ⟩} →
              x ⧗ M →
              -------------------------
              x ⧗ (↓ op V M)