open import Data.Empty
open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import AwaitingComputations
open import Preservation
open import Progress
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module Finality where


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- WITH INLINED EVALUATION CONTEXT RULES

mutual

  infix 10 _↝↝_

  data _↝↝_ {Γ : Ctx} : {C : Type} → Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

    -- COMPUTATIONAL RULES

    apply           : {X : Type}
                      {C : Type} →
                      (M : Γ ∷ X ⊢M⦂ C) →
                      (V : Γ ⊢V⦂ X) →
                      ----------------------
                      (ƛ M) · V
                      ↝↝
                      M [ id-subst [ V ]s ]m

    let-return      : {X Y : Type}
                      (V : Γ ⊢V⦂ X) →
                      (N : Γ ∷ X ⊢M⦂ Y) →
                      -----------------------------
                      let= (return V) `in N
                      ↝↝
                      N [ id-subst [ V ]s ]m

    let-↑           : {X Y : Type}
                      {op : Σₛ} →
                      (V : Γ ⊢V⦂ ``(payload op)) →
                      (M : Γ ⊢M⦂ X) →
                      (N : Γ ∷ X ⊢M⦂ Y) →
                      -----------------------------
                      let= (↑ op V M) `in N
                      ↝↝
                      ↑ op V (let= M `in N)

    let-promise     : {X Y Z : Type}
                      {op : Σₛ} →
                      (M₁ : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩) →
                      (M₂ : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                      (N : Γ ∷ Y ⊢M⦂ Z) →
                      ---------------------------------------------------------------------------
                      let= (promise op ↦ M₁ `in M₂) `in N
                      ↝↝
                      (promise op ↦ M₁ `in (let= M₂ `in (M-rename (comp-ren exchange wk₁) N)))

    promise-↑       : {X Y : Type}
                      {op op' : Σₛ} →
                      (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``(payload op')) → 
                      (M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                      --------------------------------------------
                      (promise op ↦ M `in (↑ op' V N))
                      ↝↝
                      ↑ op' (strengthen-val {Δ = X ∷ₗ []} V) (promise op ↦ M `in N)

    ↓-return        : {X : Type}
                      {op : Σₛ} →
                      (V : Γ ⊢V⦂ ``(payload op)) →
                      (W : Γ ⊢V⦂ X) →
                      ----------------------------------------------------------------
                      ↓ op V (return W)
                      ↝↝
                      return W

    ↓-↑             : {X : Type}
                      {op : Σₛ}
                      {op' : Σₛ} →
                      (V : Γ ⊢V⦂ ``(payload op)) →
                      (W : Γ ⊢V⦂ ``(payload op')) →
                      (M : Γ ⊢M⦂ X) →
                      -------------------------------
                      ↓ op V (↑ op' W M)
                      ↝↝
                      ↑ op' W (↓ op V M)


    ↓-promise-op    : {X Y : Type}
                      {op : Σₛ} →
                      (V : Γ ⊢V⦂ ``(payload op)) → 
                      (M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                      ---------------------------------------------------------------------------------------
                      ↓ op V (promise op ↦ M `in N )
                      ↝↝
                      (let= (M [ id-subst [ V ]s ]m) `in
                        ↓ op (V-rename wk₁ V) ((M-rename (comp-ren exchange wk₁) N) [ id-subst [ ` Hd ]s ]m))

    ↓-promise-op'   : {X Y : Type}
                      {op op' : Σₛ} →
                      (p : ¬ op ≡ op') →
                      (V : Γ ⊢V⦂ ``(payload op)) → 
                      (M : Γ ∷ ``(payload op') ⊢M⦂ ⟨ X ⟩) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                      ------------------------------------------------------------------------------------------
                      ↓ op V (promise op' ↦ M `in N )
                      ↝↝
                      promise op' ↦ M `in (↓ op (V-rename wk₁ V) N)

    await-promise   : {X : Type}
                      {C : Type} → 
                      (V : Γ ⊢V⦂ X) → 
                      (M : Γ ∷ X ⊢M⦂ C) →
                      --------------------
                      await ⟨ V ⟩ until M
                      ↝↝
                      M [ id-subst [ V ]s ]m

    -- INLINED EVALUATION CONTEXT RULES

    context-let      : {X Y : Type}
                       {M M' : Γ ⊢M⦂ X} →
                       {N : Γ ∷ X ⊢M⦂ Y} →
                       M ↝↝ M' → 
                       -----------------------------
                       let= M `in N
                       ↝↝
                       let= M' `in N

    context-↑        : {X : Type}
                       {op : Σₛ}
                       {V : Γ ⊢V⦂ ``(payload op)}
                       {M N : Γ ⊢M⦂ X} →
                       M ↝↝ N →
                       ---------------------------
                       ↑ op V M
                       ↝↝
                       ↑ op V N

    context-↓        : {X : Type}
                       {op : Σₛ}
                       {V : Γ ⊢V⦂ ``(payload op)}
                       {M N : Γ ⊢M⦂ X} →
                       M ↝↝ N →
                       ---------------------------
                       ↓ op V M
                       ↝↝
                       ↓ op V N

    context-promise : {X Y : Type}
                      {op : Σₛ} →
                      {M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩} →
                      {N N' : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y} →
                      N ↝↝ N' →
                      ------------------------------------------------
                      promise op ↦ M `in N
                      ↝↝
                      promise op ↦ M `in N'


-- ONE-TO-ONE CORRESPONDENCE BETWEEN THE TWO SETS OF REDUCTION RULES

↝↝-to-↝ : {Γ : Ctx}
          {C : Type}
          {M N : Γ ⊢M⦂ C} → 
          M ↝↝ N →
          -----------------
          M ↝ N

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


mutual
  ↝-context-to-↝↝ : {Γ : Ctx}
                    {Δ : BCtx}
                    {C : Type} → 
                    (E : Γ ⊢E[ Δ ]⦂ C) → 
                    {M N : (Γ ⋈ Δ) ⊢M⦂ hole-ty-e E} → 
                    M ↝ N →
                    ---------------------------
                    E [ M ] ↝↝ E [ N ]

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
  
 
  ↝-to-↝↝ : {Γ : Ctx}
            {C : Type}
            {M N : Γ ⊢M⦂ C} → 
            M ↝ N →
            -----------------
            M ↝↝ N

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
  ↝-to-↝↝ (context E r) =
    ↝-context-to-↝↝ E r


-- FINALITY OF RESULT FORMS

run-invert-let : {Γ : Ctx}
                 {X Y : Type}
                 {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X}
                 {N : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢M⦂ Y} →
                 RunResult⟨ Γ ∣ let= M `in N ⟩ →
                 -------------------------------------
                 RunResult⟨ Γ ∣ M ⟩

run-invert-let (awaiting (let-in R)) =
  awaiting R


run-invert-↓ : {Γ : Ctx}
               {X : Type}
               {op : Σₛ}
               {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ ``(payload op)}
               {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X} →
               RunResult⟨ Γ ∣ ↓ op V M ⟩ → 
               -------------------------------
               RunResult⟨ Γ ∣ M ⟩

run-invert-↓ (awaiting (interrupt await)) =
  awaiting await
run-invert-↓ (awaiting (interrupt (let-in R))) =
  awaiting (let-in R)
run-invert-↓ (awaiting (interrupt (interrupt R))) =
  awaiting (interrupt R)


run-invert-promise : {Γ : Ctx}
                     {X Y : Type}
                     {op : Σₛ}
                     {M : (⟨⟨ Γ ⟩⟩ ∷ `` (payload op)) ⊢M⦂ (⟨ X ⟩)}
                     {N : (⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩) ⊢M⦂ Y} → 
                     RunResult⟨ Γ ∣ (promise op ↦ M `in N) ⟩ →
                     --------------------------------------------------------
                     RunResult⟨ Γ ∷ X ∣ N ⟩

run-invert-promise (promise R) =
  R


run-apply-⊥ : {Γ : Ctx}
              {X : Type}
              {C : Type}
              {M : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢M⦂ C}
              {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X} →
              RunResult⟨ Γ ∣ ƛ M · V ⟩ →
              --------------------------
              ⊥

run-apply-⊥ (awaiting ())


run-↑-⊥ : {Γ : Ctx}
          {X : Type}
          {op : Σₛ}
          {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ ``(payload op)}
          {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X} → 
          RunResult⟨ Γ ∣ ↑ op V M ⟩ →
          --------------------------------
          ⊥
                 
run-↑-⊥ (awaiting ())


run-let-return-⊥ : {Γ :  Ctx}
                   {X Y : Type}
                   {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X}
                   {N : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢M⦂ Y} →
                   RunResult⟨ Γ ∣ let= return V `in N ⟩ →
                   --------------------------------------
                   ⊥

run-let-return-⊥ (awaiting (let-in ()))


run-let-promise-⊥ : {Γ : Ctx}
                    {X Y Z : Type}
                    {op : Σₛ}
                    {M₁ : (⟨⟨ Γ ⟩⟩ ∷ `` (payload op)) ⊢M⦂ (⟨ X ⟩)}
                    {M₂ : (⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩) ⊢M⦂ Y}
                    {N  : (⟨⟨ Γ ⟩⟩ ∷ Y) ⊢M⦂ Z} →
                    RunResult⟨ Γ ∣ let= promise op ↦ M₁ `in M₂ `in N ⟩ →
                    ----------------------------------------------------------
                    ⊥

run-let-promise-⊥ (awaiting (let-in ()))

run-finality-↝↝ : {Γ : Ctx}
                  {C : Type}
                  {M N : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
                  RunResult⟨ Γ ∣ M ⟩ →
                  M ↝↝ N →
                  -----------------------
                  ⊥

run-finality-↝↝ (awaiting ()) (apply M V)
run-finality-↝↝ R (let-return V N) =
  run-let-return-⊥ R
run-finality-↝↝ R (let-↑ V M N) =
  run-↑-⊥ (run-invert-let R)
run-finality-↝↝ R (let-promise M₁ M₂ N) =
  run-let-promise-⊥ R
run-finality-↝↝ (promise (awaiting ())) (promise-↑ V M N)
run-finality-↝↝ (awaiting (interrupt ())) (↓-return V W)
run-finality-↝↝ (awaiting (interrupt ())) (↓-↑ V W M)
run-finality-↝↝ (awaiting (interrupt ())) (↓-promise-op V M N)
run-finality-↝↝ (awaiting (interrupt ())) (↓-promise-op' p V M N)
run-finality-↝↝ (awaiting ()) (await-promise V M)
run-finality-↝↝ R (context-let r) =
  run-finality-↝↝ (run-invert-let R) r
run-finality-↝↝ R (context-↑ r) =
  run-↑-⊥ R
run-finality-↝↝ R (context-↓ r) =
  run-finality-↝↝ (run-invert-↓ R) r
run-finality-↝↝ R (context-promise r) =
  run-finality-↝↝ (run-invert-promise R) r


comp-finality-↝↝ : {Γ : Ctx}
                   {C : Type}
                   {M N : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
                   CompResult⟨ Γ ∣ M ⟩ →
                   M ↝↝ N →
                   -----------------------
                   ⊥

comp-finality-↝↝ (comp R) r =
  run-finality-↝↝ R r
comp-finality-↝↝ (signal R) (context-↑ r) =
  comp-finality-↝↝ R r


{- LEMMA 3.2 -}

comp-finality : {Γ : Ctx}
                {C : Type}
                {M N : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
                CompResult⟨ Γ ∣ M ⟩ →
                M ↝ N →
                -----------------------
                ⊥

comp-finality R r =
  comp-finality-↝↝ R (↝-to-↝↝ r)
