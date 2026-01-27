open import AEffFinSN.AEffSequential
open import AEffFinSN.FiniteEffectAnnotations using (op; op')

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

module AEffFinSN.AEffParallelTree where

-- TREE SHAPED PARALLEL PROCESSES

infix 10 _⊢P⦂
data _⊢P⦂ Γ : Set where

  run : Γ ⊢M⦂ C →
        ------
        Γ ⊢P⦂

  _∥_ : Γ ⊢P⦂ →
        Γ ⊢P⦂ →
        -----
        Γ ⊢P⦂

  ↑   : (op : Σₛ) →
        Γ ⊢V⦂ ```(payload op) →
        Γ ⊢P⦂ →
        -----
        Γ ⊢P⦂

  ↓   : (op : Σₛ) →
        Γ ⊢V⦂ ```(payload op) →
        Γ ⊢P⦂ →
        -----
        Γ ⊢P⦂

variable
  P P' Q Q' R R' S S' : Γ ⊢P⦂


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- WITH INLINED EVALUATION CONTEXT RULES

infix 10 _↝↝ₚ_
data _↝↝ₚ_ : Γ ⊢P⦂ → Γ ⊢P⦂ → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run     : M ↝↝ N →
            ------
            run M
            ↝↝ₚ
            run N

  -- BROADCAST RULES

  ↑-∥ₗ    : (V : Γ ⊢V⦂ ```(payload op))
            (R : Γ ⊢P⦂)
            (S : Γ ⊢P⦂) →
            ------------
            ↑ op V R ∥ S
            ↝↝ₚ
            ↑ op V (R ∥ ↓ op V S)

  ↑-∥ᵣ    : (V : Γ ⊢V⦂ ```(payload op))
            (R : Γ ⊢P⦂)
            (S : Γ ⊢P⦂) →
            --------------
            R ∥ ↑ op V S
            ↝↝ₚ
            ↑ op V (↓ op V R ∥ S)

  -- INTERRUPT PROPAGATION RULES

  ↓-run   : (V : Γ ⊢V⦂ ```(payload op))
            (M : Γ ⊢M⦂ C) →
            --------------
            ↓ op V (run M)
            ↝↝ₚ
            run (↓ op V M)

  ↓-∥     : (V : Γ ⊢V⦂ ```(payload op))
            (R : Γ ⊢P⦂)
            (S : Γ ⊢P⦂) →
            ----------------
            ↓ op V (R ∥ S)
            ↝↝ₚ
            ↓ op V R ∥ ↓ op V S

  ↓-↑     : (V : Γ ⊢V⦂ ```(payload op))
            (W : Γ ⊢V⦂ ```(payload op'))
            (R : Γ ⊢P⦂) →
            -------------------
            ↓ op V (↑ op' W R)
            ↝↝ₚ
            ↑ op' W (↓ op V R)

  -- SIGNAL HOISTING RULE

  ↑       : (V : Γ ⊢V⦂ ```(payload op))
            (M : Γ ⊢M⦂ C) →
            ---------------
            run (↑ op V M)
            ↝↝ₚ
            ↑ op V (run M)

  -- EVALUATION CONTEXT RULES

  context-∥ₗ : R ↝↝ₚ R' →
               -------
               R ∥ S
               ↝↝ₚ
               R' ∥ S

  context-∥ᵣ : S ↝↝ₚ S' →
               ------
               R ∥ S
               ↝↝ₚ
               R ∥ S'

  context-↑ : R ↝↝ₚ R' →
              ---------
              ↑ op V R
              ↝↝ₚ
              ↑ op V R'

  context-↓ : R ↝↝ₚ R' →
              ---------
              ↓ op V R
              ↝↝ₚ
              ↓ op V R'