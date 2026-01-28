open import AEffBaseSN.AEffBase.Types
open import AEffBaseSN.AEffBase.AEff
open import AEffBaseSN.AEffBase.Renamings
open import AEffBaseSN.AEffBase.Substitutions
open import AEffBaseSN.AEffBase.Preservation
open import AEffBaseSN.AEffBase.Progress

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≢_)

module AEffBaseSN.AEffBase.Finality where

-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- WITH INLINED EVALUATION CONTEXT RULES

infix 10 _↝↝_
data _↝↝_ : Γ ⊢M⦂ Y → Γ ⊢M⦂ Y → Set where

  -- COMPUTATIONAL RULES

  apply         : (M : Γ ∷ X ⊢M⦂ Y)
                  (V : Γ ⊢V⦂ X) →
                  ------------
                  ƛ M · V
                  ↝↝
                  M [ id-subst [ V ]s ]m

  let-return    : (V : Γ ⊢V⦂ X)
                  (N : Γ ∷ X ⊢M⦂ Y) →
                  ----------------
                  let= return V `in N
                  ↝↝
                  N [ id-subst [ V ]s ]m

  let-↑         : (N : Γ ∷ X ⊢M⦂ Y)
                  (V : Γ ⊢V⦂ ```(payload op))
                  (M : Γ ⊢M⦂ X) →
                  ------------
                  let= ↑ op V M `in N
                  ↝↝
                  ↑ op V (let= M `in N)

  ↓-↑           : (V' : Γ ⊢V⦂ ```(payload op'))
                  (V : Γ ⊢V⦂ ```(payload op))
                  (M : Γ ⊢M⦂ X) →
                  -------------------
                  ↓ op' V' (↑ op V M)
                  ↝↝
                  ↑ op V (↓ op' V' M)

  promise-↑     : (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op'))
                  (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                  (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                  ----------------------------
                  promise op ↦ M `in (↑ op' V N)
                  ↝↝
                  ↑ op' (strengthen-val V) (promise op ↦ M `in N)

  ↓-return      : (V : Γ ⊢V⦂ ```(payload op))
                  (W : Γ ⊢V⦂ Y) →
                  ------------
                  ↓ op V (return W)
                  ↝↝
                  return W

  let-promise   : (L : Γ ∷ Y ⊢M⦂ Z)
                  (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                  (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                  --------------------------------
                  let= promise op ↦ M `in N `in L
                  ↝↝
                  promise op ↦ M `in let= N `in M-rename (wk₂ wk₁) L

  ↓-promise-op  : (V : Γ ⊢V⦂ ```(payload op))
                  (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                  (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                  -------------------------------
                  ↓ op V (promise op ↦ M `in N)
                  ↝↝
                  let= M [ id-subst [ V ]s ]m `in ↓ op (V-rename wk₁ V) N

  ↓-promise-op' : (p : op ≢ op')
                  (V : Γ ⊢V⦂ ```(payload op'))
                  (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                  (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                  -------------------------------
                  ↓ op' V (promise op ↦ M `in N)
                  ↝↝
                  promise op ↦ M `in ↓ op' (V-rename wk₁ V) N

  let-await     : (N : Γ ∷ Y ⊢M⦂ Z) 
                  (V : Γ ⊢V⦂ ⟨ X ⟩)
                  (M : Γ ∷ X ⊢M⦂ Y) →
                  ----------------
                  let= await V until M `in N
                  ↝↝
                  await V until let= M `in M-rename (wk₂ wk₁) N

  ↓-await       : (W : Γ ⊢V⦂ ```(payload op))
                  (V : Γ ⊢V⦂ ⟨ X ⟩)
                  (M : Γ ∷ X ⊢M⦂ Y) →
                  ----------------
                  ↓ op W (await V until M)
                  ↝↝
                  await V until ↓ op (V-rename wk₁ W) M

  await-promise : (V : Γ ⊢V⦂ X)
                  (M : Γ ∷ X ⊢M⦂ Y) →
                  ----------------
                  await ⟨ V ⟩ until M
                  ↝↝
                  M [ id-subst [ V ]s ]m


  -- INLINED EVALUATION CONTEXT RULES

  context-let     : M ↝↝ M' → 
                    --------------
                    let= M `in N
                    ↝↝
                    let= M' `in N

  context-↑       : M ↝↝ N →
                    ---------
                    ↑ op V M
                    ↝↝
                    ↑ op V N

  context-↓       : M ↝↝ N →
                    ---------
                    ↓ op V M
                    ↝↝
                    ↓ op V N

  context-promise : N ↝↝ N' →
                    ---------------------
                    promise op ↦ M `in N
                    ↝↝
                    promise op ↦ M `in N'


-- ONE-TO-ONE CORRESPONDENCE BETWEEN THE TWO SETS OF REDUCTION RULES

↝↝-to-↝ : M ↝↝ N → M ↝ N
↝↝-to-↝ (apply M V) =
  apply M V
↝↝-to-↝ (let-return V N) =
  let-return V N
↝↝-to-↝ (let-↑ V M N) =
  let-↑ V M N
↝↝-to-↝ (let-promise M₁ M₂ N) =
  let-promise M₁ M₂ N
↝↝-to-↝ (promise-↑ V M N) =
  promise-↑ V M N
↝↝-to-↝ (↓-return V W) =
  ↓-return V W
↝↝-to-↝ (↓-↑ V W M) =
  ↓-↑ V W M
↝↝-to-↝ (↓-promise-op V M N) =
  ↓-promise-op V M N
↝↝-to-↝ (↓-promise-op' p V M N) =
  ↓-promise-op' p V M N
↝↝-to-↝ (let-await V M N) =
  let-await V M N
↝↝-to-↝ (↓-await V W M) =
  ↓-await V W M
↝↝-to-↝ (await-promise V M) =
  await-promise V M
↝↝-to-↝ (context-let r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-↑ r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-↓ r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-promise r) =
  context _ (↝↝-to-↝ r)


↝-context-to-↝↝ : (E : Γ ⊢E[ Δb ]⦂ X) → 
                  {M N : Γ ⋈ Δb ⊢M⦂ hole-ty-e E} → 
                  M ↝ N →
                  ------------------
                  E [ M ] ↝↝ E [ N ]

↝-to-↝↝ : M ↝ N → M ↝↝ N

↝-context-to-↝↝ [-] r =
  ↝-to-↝↝ r
↝-context-to-↝↝ (let= E `in x) r =
  context-let (↝-context-to-↝↝ E r)
↝-context-to-↝↝ (↑ op V E) r =
  context-↑ (↝-context-to-↝↝ E r)
↝-context-to-↝↝ (↓ op V E) r =
  context-↓ (↝-context-to-↝↝ E r)
↝-context-to-↝↝ (promise op ↦ M `in E) r =
  context-promise (↝-context-to-↝↝ E r)

↝-to-↝↝ (apply M V) =
  apply M V
↝-to-↝↝ (let-return V N) =
  let-return V N
↝-to-↝↝ (let-↑ V M N) =
  let-↑ V M N
↝-to-↝↝ (let-promise M₁ M₂ N) =
  let-promise M₁ M₂ N
↝-to-↝↝ (promise-↑ V M N) =
  promise-↑ V M N
↝-to-↝↝ (↓-return V W) =
  ↓-return V W
↝-to-↝↝ (↓-↑ V W M) =
  ↓-↑ V W M
↝-to-↝↝ (↓-promise-op V M N) =
  ↓-promise-op V M N
↝-to-↝↝ (↓-promise-op' p V M N) =
  ↓-promise-op' p V M N
↝-to-↝↝ (await-promise V M) =
  await-promise V M
↝-to-↝↝ (let-await N V M) =
  let-await N V M
↝-to-↝↝ (↓-await W V M) =
  ↓-await W V M
↝-to-↝↝ (context E r) = 
  ↝-context-to-↝↝ E r


-- FINALITY OF RESULT FORMS

run-finality-↝↝ : RunResult⟨ Γ ∣ M ⟩ →
                  M ↝↝ N →
                  -----
                  ⊥

run-finality-↝↝ (promise R) (context-promise r) = run-finality-↝↝ R r

comp-finality-↝↝ : CompResult⟨ Γ ∣ M ⟩ →
                   M ↝↝ N →
                   -----
                   ⊥

comp-finality-↝↝ (comp R) r =
  run-finality-↝↝ R r
comp-finality-↝↝ (signal R) (context-↑ r) =
  comp-finality-↝↝ R r


comp-finality : CompResult⟨ Γ ∣ M ⟩ →
                M ↝ N →
                -----
                ⊥

comp-finality R r =
  comp-finality-↝↝ R (↝-to-↝↝ r)