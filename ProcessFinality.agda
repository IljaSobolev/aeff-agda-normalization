open import Data.Empty
open import Data.List renaming (_∷_ to _∷ₗ_ ; [_] to [_]ₗ)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import AwaitingComputations
open import Finality
open import Preservation
open import ProcessPreservation
open import ProcessProgress
open import Progress
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module ProcessFinality where

-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- WITH INLINED EVALUATION CONTEXT RULES

infix 10 _↝↝P_

data _↝↝P_ {Γ : Ctx} : {PP : PType} → Γ ⊢P⦂ PP → Γ ⊢P⦂ PP → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run   : {X : Type}
          {M N : Γ ⊢M⦂ X} → 
          M ↝↝ N →
          ---------------------------
          (run M) ↝↝P (run N)

  -- BROADCAST RULES

  ↑-∥ₗ   : {PP : PType}
           {QQ : PType}
           {op : Σₛ} → 
           (V : Γ ⊢V⦂ `` (payload op)) →
           (P : Γ ⊢P⦂ PP) →
           (Q : Γ ⊢P⦂ QQ) →
           ------------------------------------------
           ((↑ op V P) ∥ Q)
           ↝↝P
           ↑ op V (P ∥ ↓ op V Q)

  ↑-∥ᵣ   : {PP : PType}
           {QQ : PType}
           {op : Σₛ} → 
           (V : Γ ⊢V⦂ `` (payload op)) →
           (P : Γ ⊢P⦂ PP) →
           (Q : Γ ⊢P⦂ QQ) →
           ------------------------------------------
           (P ∥ (↑ op V Q))
           ↝↝P
           ↑ op V (↓ op V P ∥ Q)

  -- INTERRUPT PROPAGATION RULES

  ↓-run : {X : Type}
          {op : Σₛ} → 
          (V : Γ ⊢V⦂ `` (payload op)) → 
          (M : Γ ⊢M⦂ X) →
          -----------------------------
          ↓ op V (run M)
          ↝↝P
          run (↓ op V M)

  ↓-∥   : {PP : PType}
          {QQ : PType}
          {op : Σₛ}
          (V : Γ ⊢V⦂ `` (payload op)) →
          (P : Γ ⊢P⦂ PP) →
          (Q : Γ ⊢P⦂ QQ) →
          -----------------------------
          ↓ op V (P ∥ Q)
          ↝↝P
          ((↓ op V P) ∥ (↓ op V Q))

  ↓-↑   : {PP : PType}
          {op : Σₛ}
          {op' : Σₛ} →
          (V : Γ ⊢V⦂ ``(payload op)) →
          (W : Γ ⊢V⦂ ``(payload op')) →
          (P : Γ ⊢P⦂ PP) →
          -----------------------------------
          ↓ op V (↑ op' W P)
          ↝↝P
          ↑ op' W (↓ op V P)

  -- SIGNAL HOISTING RULE

  ↑     : {X : Type}
          {op : Σₛ}
          (V : Γ ⊢V⦂ `` (payload op))
          (M : Γ ⊢M⦂ X) →
          -----------------------------
          run (↑ op V M)
          ↝↝P
          ↑ op V (run M)

  -- EVALUATION CONTEXT RULES

  context-∥ₗ : {PP : PType}
               {QQ : PType}
               {P : Γ ⊢P⦂ PP}
               {P' : Γ ⊢P⦂ PP}
               {Q : Γ ⊢P⦂ QQ} →
               P ↝↝P P' → 
               ------------------
               P ∥ Q
               ↝↝P
               P' ∥ Q

  context-∥ᵣ : {PP : PType}
               {QQ : PType}
               {P : Γ ⊢P⦂ PP}
               {Q : Γ ⊢P⦂ QQ}
               {Q' : Γ ⊢P⦂ QQ} →
               Q ↝↝P Q' → 
               ------------------
               P ∥ Q
               ↝↝P
               P ∥ Q'

  context-↑ : {PP : PType}
              {op : Σₛ}
              {V : Γ ⊢V⦂ ``(payload op)}
              {P : Γ ⊢P⦂ PP}
              {P' : Γ ⊢P⦂ PP} →
              P ↝↝P P' →
              --------------------------
              ↑ op V P
              ↝↝P
              ↑ op V P'

  context-↓ : {PP : PType}
              {op : Σₛ}
              {V : Γ ⊢V⦂ ``(payload op)}
              {P : Γ ⊢P⦂ PP}
              {P' : Γ ⊢P⦂ PP} →
              P ↝↝P P' →
              ----------------------
              ↓ op V P
              ↝↝P
              ↓ op V P'


-- ONE-TO-ONE CORRESPONDENCE BETWEEN THE TWO SETS OF REDUCTION RULES

[]↝↝P-to-[]↝P : {Γ : Ctx}
                {PP : PType}
                {P : Γ ⊢P⦂ PP}
                {Q : Γ ⊢P⦂ PP} →
                P ↝↝P Q →
                -----------------
                P ↝P Q

[]↝↝P-to-[]↝P (run r) =
  run (↝↝-to-↝ r)
[]↝↝P-to-[]↝P (↑-∥ₗ V P Q) =
  ↑-∥ₗ V P Q
[]↝↝P-to-[]↝P (↑-∥ᵣ V P Q) =
  ↑-∥ᵣ V P Q
[]↝↝P-to-[]↝P (↓-run V M) =
  ↓-run V M
[]↝↝P-to-[]↝P (↓-∥ V P Q) =
  ↓-∥ V P Q
[]↝↝P-to-[]↝P (↓-↑ V W P) =
  ↓-↑ V W P
[]↝↝P-to-[]↝P (↑ V M) =
  ↑ V M
[]↝↝P-to-[]↝P (context-∥ₗ r) =
  context (_ ∥ₗ _) ([]↝↝P-to-[]↝P r)
[]↝↝P-to-[]↝P (context-∥ᵣ r) =
  context (_ ∥ᵣ _) ([]↝↝P-to-[]↝P r)
[]↝↝P-to-[]↝P (context-↑ r) =
  context (↑ _ _ _) ([]↝↝P-to-[]↝P r)
[]↝↝P-to-[]↝P (context-↓ r) =
  context (↓ _ _ _) ([]↝↝P-to-[]↝P r)


mutual

  []↝P-context-to-[]↝↝P : {Γ : Ctx}
                          {PP : PType}
                          (F : Γ ⊢F⦂ PP)
                          {P : Γ ⊢P⦂ (hole-ty-f F)}
                          {Q : Γ ⊢P⦂ (hole-ty-f F)} →
                          P ↝P Q →
                          -----------------------------------------------------------------------------
                          F [ P ]f
                          ↝↝P
                          F [ Q ]f

  []↝P-context-to-[]↝↝P [-] r =
    []↝P-to-[]↝↝P r
  []↝P-context-to-[]↝↝P (F ∥ₗ Q) r =
    context-∥ₗ ([]↝P-context-to-[]↝↝P F r)
  []↝P-context-to-[]↝↝P (P ∥ᵣ F) r =
    context-∥ᵣ ([]↝P-context-to-[]↝↝P F r)
  []↝P-context-to-[]↝↝P (↑ op V F) r = 
    context-↑ ([]↝P-context-to-[]↝↝P F r)
  []↝P-context-to-[]↝↝P (↓ op V F) r =
    context-↓ ([]↝P-context-to-[]↝↝P F r)


  []↝P-to-[]↝↝P : {Γ : Ctx}
                  {PP : PType}
                  {P : Γ ⊢P⦂ PP}
                  {Q : Γ ⊢P⦂ PP} →
                  P ↝P Q →
                  -----------------
                  P ↝↝P Q

  []↝P-to-[]↝↝P (run r) =
    run (↝-to-↝↝ r)
  []↝P-to-[]↝↝P (↑-∥ₗ V P Q) =
    ↑-∥ₗ V P Q
  []↝P-to-[]↝↝P (↑-∥ᵣ V P Q) =
    ↑-∥ᵣ V P Q
  []↝P-to-[]↝↝P (↓-run V M) =
    ↓-run V M
  []↝P-to-[]↝↝P (↓-∥ V P Q) =
    ↓-∥ V P Q
  []↝P-to-[]↝↝P (↓-↑ V W P) =
    ↓-↑ V W P
  []↝P-to-[]↝↝P (↑ V M) =
    ↑ V M
  []↝P-to-[]↝↝P (context F r) =
    []↝P-context-to-[]↝↝P _ r


-- FINALITY OF RESULT FORMS

par-finality-↝↝P : {PP : PType}
                  {P : [] ⊢P⦂ PP} → 
                  {Q : [] ⊢P⦂ PP} → 
                  ParResult⟨ P ⟩ →
                  P ↝↝P Q →
                  -----------------
                  ⊥

par-finality-↝↝P (run R) (run r) =
  run-finality-↝↝ R r 
par-finality-↝↝P (run R) (↑ V M) =
  run-↑-⊥ R
par-finality-↝↝P (par R S) (context-∥ₗ r') =
  par-finality-↝↝P R r'
par-finality-↝↝P (par R S) (context-∥ᵣ r') =
  par-finality-↝↝P S r'


proc-finality-↝↝P : {PP : PType}
                  {P : [] ⊢P⦂ PP} → 
                  {Q : [] ⊢P⦂ PP} → 
                  ProcResult⟨ P ⟩ →
                  P ↝↝P Q →
                  -----------------
                  ⊥

proc-finality-↝↝P (proc R) r' =
  par-finality-↝↝P R r'
proc-finality-↝↝P (signal R) (context-↑ r') =
  proc-finality-↝↝P R r'


{- LEMMA 4.2 -}

proc-finality : {PP : PType}
                {P : [] ⊢P⦂ PP} → 
                {Q : [] ⊢P⦂ PP} → 
                ProcResult⟨ P ⟩ →
                P ↝P Q →
                -----------------
                ⊥

proc-finality R r' =
  proc-finality-↝↝P R ([]↝P-to-[]↝↝P r')
