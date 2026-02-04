open import AEffFinFlatSN.AEffSequential
open import AEffFinFlatSN.FiniteEffectAnnotations using (op)

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

module AEffFinFlatSN.AEffParallelFlat where

-- FLATTENED PARALLEL PROCESSES

infix 10 _⊢P⦂
data _⊢P⦂ Γ : Set where
  []  : Γ ⊢P⦂
  _∥_ : Γ ⊢M⦂ C → Γ ⊢P⦂ → Γ ⊢P⦂

variable
  P P' Q Q' : Γ ⊢P⦂


-- APPLYING AN INTERRUPT TO ALL COMPUTATIONS IN A PARALLEL PROCESS

↓ₜ : (op : Σₛ) → Γ ⊢V⦂ ```(payload op) → Γ ⊢P⦂ → Γ ⊢P⦂
↓ₜ op V [] = []
↓ₜ op V (M ∥ P) = ↓ op V M ∥ ↓ₜ op V P


-- THE REDUCTION THAT SENDS A SIGNAL FROM A COMPUTATION TO ALL THE OTHER COMPUTATIONS IN ONE STEP

infix 10 _↝↝ₚ-[_,_]_
data _↝↝ₚ-[_,_]_ : Γ ⊢P⦂ → (op : Σₛ) → Γ ⊢V⦂ ```(payload op) → Γ ⊢P⦂ → Set where

  ↑-∥ₗ : ----------------------
         ↑ op V M ∥ (N ∥ P)
         ↝↝ₚ-[ op , V ]
         M ∥ (↓ op V N ∥ ↓ₜ op V P)

  ↑-∥ᵣ : P ↝↝ₚ-[ op , V ] Q →
         -------------
         M ∥ P
         ↝↝ₚ-[ op , V ]
         ↓ op V M ∥ Q


-- THE REDUCTION THAT RUNS ONE OF THE COMPUTATION IN A PARALLEL PROCESS

infix 10 _↝↝ₚ-↝_
data _↝↝ₚ-↝_ : Γ ⊢P⦂ → Γ ⊢P⦂ → Set where

  context-∥ₗ : M ↝↝ N →
               -----
               M ∥ P
               ↝↝ₚ-↝
               N ∥ P

  context-∥ᵣ : P ↝↝ₚ-↝ Q →
               -----
               M ∥ P
               ↝↝ₚ-↝
               M ∥ Q


-- A REDUCTION OF A PARALLEL PROCESS IS EITHER A REDUCTION IN ONE OF THE COMPUTATION
-- OR THE SENDING OF A SIGNALS FROM ONE COMPUTATION TO ALL THE OTHERS

infix 10 _↝↝ₚ_
data _↝↝ₚ_ : Γ ⊢P⦂ → Γ ⊢P⦂ → Set where
  ↑-∥ : P ↝↝ₚ-[ op , V ] Q → P ↝↝ₚ Q
  run : P ↝↝ₚ-↝ Q → P ↝↝ₚ Q