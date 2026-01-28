open import AEffBaseSN.AEffBase.Types
open import AEffBaseSN.AEffBase.AEff
open import AEffBaseSN.AEffBase.Preservation

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

module AEffBaseSN.AEffBase.ProcessPreservation where

-- EVALUATION CONTEXTS FOR PROCESSES

infix 10 _⊢F⦂_
data _⊢F⦂_ (Γ : Ctx) : PType → Set where

  [-]  : --------
         Γ ⊢F⦂ PP

  _∥ₗ_ : Γ ⊢F⦂ PP →
         Γ ⊢P⦂ QQ →
         -------------
         Γ ⊢F⦂ PP ∥ QQ

  _∥ᵣ_ : Γ ⊢P⦂ PP →
         Γ ⊢F⦂ QQ →
         -------------
         Γ ⊢F⦂ PP ∥ QQ

  ↑    : (op : Σₛ) →
         Γ ⊢V⦂ ```(payload op) →
         Γ ⊢F⦂ PP →
         --------
         Γ ⊢F⦂ PP

  ↓    : (op : Σₛ) →
         Γ ⊢V⦂ ```(payload op) →
         Γ ⊢F⦂ PP →
         --------
         Γ ⊢F⦂ PP


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED PROCESS EVALUATION CONTEXT

hole-ty-f : Γ ⊢F⦂ PP → PType
hole-ty-f {PP = PP} [-] = PP
hole-ty-f (F ∥ₗ Q ) = hole-ty-f F
hole-ty-f (P ∥ᵣ F) = hole-ty-f F
hole-ty-f (↑ op V F) = hole-ty-f F
hole-ty-f (↓ op V F) = hole-ty-f F


-- FILLING A WELL-TYPED PROCESS EVALUATION CONTEXT

infix 30 _[_]f
_[_]f : (F : Γ ⊢F⦂ PP) → Γ ⊢P⦂ hole-ty-f F → Γ ⊢P⦂ PP
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

infix 10 _↝ₚ_
data _↝ₚ_ : Γ ⊢P⦂ PP → Γ ⊢P⦂ PP → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run     : M ↝ N →
            ------
            run M
            ↝ₚ
            run N

  -- BROADCAST RULES

  ↑-∥ₗ    : (V : Γ ⊢V⦂ ```(payload op))
            (P : Γ ⊢P⦂ PP)
            (Q : Γ ⊢P⦂ QQ) →
            ------------
            ↑ op V P ∥ Q
            ↝ₚ
            ↑ op V (P ∥ ↓ op V Q)

  ↑-∥ᵣ    : (V : Γ ⊢V⦂ ```(payload op))
            (P : Γ ⊢P⦂ PP)
            (Q : Γ ⊢P⦂ QQ) →
            --------------
            P ∥ ↑ op V Q
            ↝ₚ
            ↑ op V (↓ op V P ∥ Q)

  -- INTERRUPT PROPAGATION RULES

  ↓-run   : (V : Γ ⊢V⦂ ```(payload op))
            (M : Γ ⊢M⦂ X) →
            --------------
            ↓ op V (run M)
            ↝ₚ
            run (↓ op V M)

  ↓-∥     : (V : Γ ⊢V⦂ ```(payload op))
            (P : Γ ⊢P⦂ PP)
            (Q : Γ ⊢P⦂ QQ) →
            ----------------
            ↓ op V (P ∥ Q)
            ↝ₚ
            ↓ op V P ∥ ↓ op V Q

  ↓-↑     : (V : Γ ⊢V⦂ ```(payload op))
            (W : Γ ⊢V⦂ ```(payload op'))
            (P : Γ ⊢P⦂ PP) →
            -------------------
            ↓ op V (↑ op' W P)
            ↝ₚ
            ↑ op' W (↓ op V P)

  -- SIGNAL HOISTING RULE

  ↑       : (V : Γ ⊢V⦂ ```(payload op))
            (M : Γ ⊢M⦂ X) →
            ---------------
            run (↑ op V M)
            ↝ₚ
            ↑ op V (run M)

  -- EVALUATION CONTEXT RULE

  context : (F : Γ ⊢F⦂ PP)
            {P Q : Γ ⊢P⦂ hole-ty-f F} →
            P ↝ₚ Q →
            --------
            F [ P ]f
            ↝ₚ
            F [ Q ]f