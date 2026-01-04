open import AEffBaseSN.AEffBase.Types
open import AEffBaseSN.AEffBase.AEff
open import AEffBaseSN.AEffBase.Finality
open import AEffBaseSN.AEffBase.ProcessPreservation
open import AEffBaseSN.AEffBase.ProcessProgress

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

open import Data.Empty using (⊥)

module AEffBaseSN.AEffBase.ProcessFinality where

-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- WITH INLINED EVALUATION CONTEXT RULES

infix 10 _↝↝ₚ_
data _↝↝ₚ_ : Γ ⊢P⦂ PP → Γ ⊢P⦂ PP → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run     : M ↝↝ N →
            ------
            run M
            ↝↝ₚ
            run N

  -- BROADCAST RULES

  ↑-∥ₗ    : (V : Γ ⊢V⦂ ```(payload op))
            (P : Γ ⊢P⦂ PP)
            (Q : Γ ⊢P⦂ QQ) →
            ------------
            ↑ op V P ∥ Q
            ↝↝ₚ
            ↑ op V (P ∥ ↓ op V Q)

  ↑-∥ᵣ    : (V : Γ ⊢V⦂ ```(payload op))
            (P : Γ ⊢P⦂ PP)
            (Q : Γ ⊢P⦂ QQ) →
            --------------
            P ∥ ↑ op V Q
            ↝↝ₚ
            ↑ op V (↓ op V P ∥ Q)

  -- INTERRUPT PROPAGATION RULES

  ↓-run   : (V : Γ ⊢V⦂ ```(payload op))
            (M : Γ ⊢M⦂ X) →
            --------------
            ↓ op V (run M)
            ↝↝ₚ
            run (↓ op V M)

  ↓-∥     : (V : Γ ⊢V⦂ ```(payload op))
            (P : Γ ⊢P⦂ PP)
            (Q : Γ ⊢P⦂ QQ) →
            ----------------
            ↓ op V (P ∥ Q)
            ↝↝ₚ
            ↓ op V P ∥ ↓ op V Q

  ↓-↑     : (V : Γ ⊢V⦂ ```(payload op))
            (W : Γ ⊢V⦂ ```(payload op'))
            (P : Γ ⊢P⦂ PP) →
            -------------------
            ↓ op V (↑ op' W P)
            ↝↝ₚ
            ↑ op' W (↓ op V P)

  -- SIGNAL HOISTING RULE

  ↑       : (V : Γ ⊢V⦂ ```(payload op))
            (M : Γ ⊢M⦂ X) →
            ---------------
            run (↑ op V M)
            ↝↝ₚ
            ↑ op V (run M)

  -- EVALUATION CONTEXT RULES

  context-∥ₗ : P ↝↝ₚ P' → 
               -------
               P ∥ Q
               ↝↝ₚ
               P' ∥ Q

  context-∥ᵣ : Q ↝↝ₚ Q' → 
               ------
               P ∥ Q
               ↝↝ₚ
               P ∥ Q'

  context-↑ : P ↝↝ₚ P' →
              ---------
              ↑ op V P
              ↝↝ₚ
              ↑ op V P'

  context-↓ : P ↝↝ₚ P' →
              ---------
              ↓ op V P
              ↝↝ₚ
              ↓ op V P'


-- ONE-TO-ONE CORRESPONDENCE BETWEEN THE TWO SETS OF REDUCTION RULES

↝↝ₚ-to-↝ₚ : P ↝↝ₚ Q → P ↝ₚ Q
↝↝ₚ-to-↝ₚ (run r) =
  run (↝↝-to-↝ r)
↝↝ₚ-to-↝ₚ (↑-∥ₗ V P Q) =
  ↑-∥ₗ V P Q
↝↝ₚ-to-↝ₚ (↑-∥ᵣ V P Q) =
  ↑-∥ᵣ V P Q
↝↝ₚ-to-↝ₚ (↓-run V M) =
  ↓-run V M
↝↝ₚ-to-↝ₚ (↓-∥ V P Q) =
  ↓-∥ V P Q
↝↝ₚ-to-↝ₚ (↓-↑ V W P) =
  ↓-↑ V W P
↝↝ₚ-to-↝ₚ (↑ V M) =
  ↑ V M
↝↝ₚ-to-↝ₚ (context-∥ₗ r) =
  context (_ ∥ₗ _) (↝↝ₚ-to-↝ₚ r)
↝↝ₚ-to-↝ₚ (context-∥ᵣ r) =
  context (_ ∥ᵣ _) (↝↝ₚ-to-↝ₚ r)
↝↝ₚ-to-↝ₚ (context-↑ r) =
  context (↑ _ _ _) (↝↝ₚ-to-↝ₚ r)
↝↝ₚ-to-↝ₚ (context-↓ r) =
  context (↓ _ _ _) (↝↝ₚ-to-↝ₚ r)


↝ₚ-context-to-↝↝ₚ : (F : Γ ⊢F⦂ PP)
                    {P Q : Γ ⊢P⦂ hole-ty-f F} →
                    P ↝ₚ Q →
                    --------
                    F [ P ]f
                    ↝↝ₚ
                    F [ Q ]f

↝ₚ-to-↝↝ₚ : P ↝ₚ Q → P ↝↝ₚ Q

↝ₚ-context-to-↝↝ₚ [-] r =
  ↝ₚ-to-↝↝ₚ r
↝ₚ-context-to-↝↝ₚ (F ∥ₗ Q) r =
  context-∥ₗ (↝ₚ-context-to-↝↝ₚ F r)
↝ₚ-context-to-↝↝ₚ (P ∥ᵣ F) r =
  context-∥ᵣ (↝ₚ-context-to-↝↝ₚ F r)
↝ₚ-context-to-↝↝ₚ (↑ op V F) r = 
  context-↑ (↝ₚ-context-to-↝↝ₚ F r)
↝ₚ-context-to-↝↝ₚ (↓ op V F) r =
  context-↓ (↝ₚ-context-to-↝↝ₚ F r)

↝ₚ-to-↝↝ₚ (run r) =
  run (↝-to-↝↝ r)
↝ₚ-to-↝↝ₚ (↑-∥ₗ V P Q) =
  ↑-∥ₗ V P Q
↝ₚ-to-↝↝ₚ (↑-∥ᵣ V P Q) =
  ↑-∥ᵣ V P Q
↝ₚ-to-↝↝ₚ (↓-run V M) =
  ↓-run V M
↝ₚ-to-↝↝ₚ (↓-∥ V P Q) =
  ↓-∥ V P Q
↝ₚ-to-↝↝ₚ (↓-↑ V W P) =
  ↓-↑ V W P
↝ₚ-to-↝↝ₚ (↑ V M) =
  ↑ V M
↝ₚ-to-↝↝ₚ (context F r) =
  ↝ₚ-context-to-↝↝ₚ F r


-- FINALITY OF RESULT FORMS

par-finality-↝↝ₚ : ParResult⟨ P ⟩ →
                   P ↝↝ₚ Q →
                   --------
                   ⊥
par-finality-↝↝ₚ (run R) (run r) =
  run-finality-↝↝ R r 
par-finality-↝↝ₚ (run ()) (↑ V M)
par-finality-↝↝ₚ (par R S) (context-∥ₗ r') =
  par-finality-↝↝ₚ R r'
par-finality-↝↝ₚ (par R S) (context-∥ᵣ r') =
  par-finality-↝↝ₚ S r'


proc-finality-↝↝ₚ : ProcResult⟨ P ⟩ →
                    P ↝↝ₚ Q →
                    -----
                    ⊥
proc-finality-↝↝ₚ (proc R) r' =
  par-finality-↝↝ₚ R r'
proc-finality-↝↝ₚ (signal R) (context-↑ r') =
  proc-finality-↝↝ₚ R r'


{- LEMMA 4.2 -}

proc-finality : ProcResult⟨ P ⟩ →
                P ↝ₚ Q →
                -------
                ⊥
proc-finality R r =
  proc-finality-↝↝ₚ R (↝ₚ-to-↝↝ₚ r)