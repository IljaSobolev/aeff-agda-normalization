{-# OPTIONS --guardedness #-}

open import Data.Empty
open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEffReinstSN.AEff
open import AEffReinstSN.CoinductiveEffectAnnotations
open import AEffReinstSN.Preservation
open import AEffReinstSN.Progress
open import AEffReinstSN.Renamings
open import AEffReinstSN.Substitutions
open import AEffReinstSN.Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module AEffReinstSN.Finality where


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- WITH INLINED EVALUATION CONTEXT RULES

mutual

  infix 10 _↝↝_

  data _↝↝_ {Γ : Ctx} : {C : CType} → Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

    -- COMPUTATIONAL RULES

    apply           : {X : VType}
                      {C : CType} →
                      (M : Γ ∷ X ⊢M⦂ C) →
                      (V : Γ ⊢V⦂ X) →
                      ----------------------
                      (ƛ M) · V
                      ↝↝
                      M [ id-subst [ V ]s ]m

    let-return      : {X Y : VType}
                      {o : O}
                      {i : I} → 
                      (V : Γ ⊢V⦂ X) →
                      (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                      -----------------------------
                      let= (return V) `in N
                      ↝↝
                      N [ id-subst [ V ]s ]m

    let-↑           : {X Y : VType}
                      {o : O}
                      {i : I}
                      {op : Σₛ} →
                      (p : op ∈ₒ o) →
                      (V : Γ ⊢V⦂ ```(payload op)) →
                      (M : Γ ⊢M⦂ X ! (o , i)) →
                      (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                      -----------------------------
                      let= (↑ op p V M) `in N
                      ↝↝
                      ↑ op p V (let= M `in N)

    let-promise     : {X Y Z : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      (p : just (o' , i') ⊑-aux lkpᵢ op i) →
                      (q : (∅ᵢ [ op ↦ just (o' , i') ]ᵢ) ⊑ᵢ i') →
                      (M₁ : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙 ! (o' , i')) →
                      (M₂ : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                      (N : Γ ∷ Y ⊢M⦂ Z ! (o , i)) →
                      ---------------------------------------------------------------------------
                      let= (promise op ∣ p , q ↦ M₁ `in M₂) `in N
                      ↝↝
                      (promise op ∣ p , q ↦ M₁ `in (let= M₂ `in (M-rename (wk₂ wk₁) N)))

    let-await       : {X Y Z : VType}
                      {o : O}
                      {i : I} →
                      (V : Γ ⊢V⦂ ⟨ X ⟩) →
                      (M : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                      (N : Γ ∷ Y ⊢M⦂ Z ! (o , i)) →
                      -------------------------------------------------------
                      let= (await V until M) `in N
                      ↝↝
                      await V until (let= M `in M-rename (wk₂ wk₁) N)

    promise-↑       : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op op' : Σₛ} →
                      (p : just (o' , i') ⊑-aux lkpᵢ op i) →
                      (q : (∅ᵢ [ op ↦ just (o' , i') ]ᵢ) ⊑ᵢ i') →
                      (r : op' ∈ₒ o) →
                      (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op')) → 
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙 ! (o' , i')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                      --------------------------------------------
                      (promise op ∣ p , q ↦ M `in (↑ op' r V N))
                      ↝↝
                      ↑ op' r (strengthen-val {Δ = X ∷ₗ []} V) (promise op ∣ p , q ↦ M `in N)

    ↓-return        : {X : VType}
                      {o : O}
                      {i : I}
                      {op : Σₛ} →
                      (V : Γ ⊢V⦂ ```(payload op)) →
                      (W : Γ ⊢V⦂ X) →
                      ----------------------------------------------------------------
                      ↓ {o = o} {i = i} op V (return W)
                      ↝↝
                      return {o = proj₁ (op ↓ₑ (o , i))} {i = proj₂ (op ↓ₑ (o , i))} W

    ↓-↑             : {X : VType}
                      {o : O}
                      {i : I}
                      {op : Σₛ}
                      {op' : Σₛ} →
                      (p : op' ∈ₒ o) →
                      (V : Γ ⊢V⦂ ```(payload op)) →
                      (W : Γ ⊢V⦂ ```(payload op')) →
                      (M : Γ ⊢M⦂ X ! (o , i)) →
                      -------------------------------
                      ↓ op V (↑ op' p W M)
                      ↝↝
                      ↑ op' (↓ₑ-⊑ₒ {i = i} op' p) W (↓ op V M)

    ↓-promise-op    : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      (p : just (o' , i') ⊑-aux imap i op) →
                      (q : (∅ᵢ [ op ↦ just (o' , i') ]ᵢ) ⊑ᵢ i') →
                      (V : Γ ⊢V⦂ ```(payload op)) → 
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙 ! (o' , i')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                      ---------------------------------------------------------------------------------------
                      ↓ op V (promise op ∣ p , q ↦ M `in N)
                      ↝↝
                      (let= (let= coerce (o⊑ {i = i} p) (i⊑ {i = i} {o = o} p)
                          (M [ id-subst [ V ]s ]m) `in
                              match+ (` Hd)
                                  (return (` Hd))
                                  (coerce (λ _ ()) (⊑ᵢ-trans q (i⊑ {i = i} {o = o} p)) (M-rename wk₁ (M-rename wk₁
                                      (promise_∣_,_↦_`in_ {o = ∅ₒ} op
                                        (subst (_ ⊑-aux_) (sym ite-≡) (⊑ₒ-refl , ⊑ᵢ-refl)) q M (return (` Hd))))))) `in
                                    ↓ op (V-rename wk₁ V) N)

    ↓-promise-op'   : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op op' : Σₛ} →
                      (p : ¬ op ≡ op') →
                      (q : just (o' , i') ⊑-aux lkpᵢ op' i) →
                      (r : (∅ᵢ [ op' ↦ just (o' , i') ]ᵢ) ⊑ᵢ i') →
                      (V : Γ ⊢V⦂ ```(payload op)) → 
                      (M : Γ ∷ ```(payload op') ⊢M⦂ ⟨ X ⟩ + 𝟙 ! (o' , i')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                      ------------------------------------------------------------------------------------------
                      ↓ op V (promise op' ∣ q , r ↦ M `in N )
                      ↝↝
                      promise op' ∣ ⊑-aux-trans _ _ _ q (lkpᵢ-↓ₑ-neq-⊑ {i = i} {o = o} p) , r ↦ M `in (↓ op (V-rename wk₁ V) N)

    ↓-await         : {X Y : VType}
                      {o : O}
                      {i : I}
                      {op : Σₛ} →
                      (V : Γ ⊢V⦂ ```(payload op)) →
                      (W : Γ ⊢V⦂ ⟨ X ⟩) →
                      (M : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                      ------------------------------------------
                      ↓ op V (await W until M)
                      ↝↝
                      await W until (↓ op (V-rename wk₁ V) M)

    match+-inl      : {X Y : VType}
                      {C : CType}
                      (V : Γ ⊢V⦂ X)
                      (M : Γ ∷ X ⊢M⦂ C)
                      (N : Γ ∷ Y ⊢M⦂ C) →
                      ------------------
                      match+ (inl V) M N
                      ↝↝
                      M [ id-subst [ V ]s ]m

    match+-inr      : {X Y : VType}
                      {C : CType}
                      (V : Γ ⊢V⦂ Y)
                      (M : Γ ∷ X ⊢M⦂ C)
                      (N : Γ ∷ Y ⊢M⦂ C) →
                      ------------------
                      match+ (inr V) M N
                      ↝↝
                      N [ id-subst [ V ]s ]m

    await-promise   : {X : VType}
                      {C : CType} → 
                      (V : Γ ⊢V⦂ X) → 
                      (M : Γ ∷ X ⊢M⦂ C) →
                      --------------------
                      await ⟨ V ⟩ until M
                      ↝↝
                      M [ id-subst [ V ]s ]m

    -- INLINED EVALUATION CONTEXT RULES

    context-let      : {X Y : VType}
                       {o : O}
                       {i : I} → 
                       {M M' : Γ ⊢M⦂ X ! (o , i)} →
                       {N : Γ ∷ X ⊢M⦂ Y ! (o , i)} →
                       M ↝↝ M' → 
                       -----------------------------
                       let= M `in N
                       ↝↝
                       let= M' `in N

    context-↑        : {X : VType}
                       {o : O}
                       {i : I}
                       {op : Σₛ}
                       {p : op ∈ₒ o}
                       {V : Γ ⊢V⦂ ```(payload op)}
                       {M N : Γ ⊢M⦂ X ! (o , i)} →
                       M ↝↝ N →
                       ---------------------------
                       ↑ op p V M
                       ↝↝
                       ↑ op p V N

    context-↓        : {X : VType}
                       {o : O}
                       {i : I}
                       {op : Σₛ}
                       {V : Γ ⊢V⦂ ```(payload op)}
                       {M N : Γ ⊢M⦂ X ! (o , i)} →
                       M ↝↝ N →
                       ---------------------------
                       ↓ op V M
                       ↝↝
                       ↓ op V N

    context-promise : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      {r : just (o' , i') ⊑-aux lkpᵢ op i}
                      {q : (∅ᵢ [ op ↦ just (o' , i') ]ᵢ) ⊑ᵢ i'} →
                      {M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙 ! (o' , i')} →
                      {N N' : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
                      N ↝↝ N' →
                      ------------------------------------------------
                      promise op ∣ r , q ↦ M `in N
                      ↝↝
                      promise op ∣ r , q ↦ M `in N'

    context-coerce  : {X : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'} → 
                      {M N : Γ ⊢M⦂ X ! (o , i)} →
                      M ↝↝ N →
                      ---------------------------
                      coerce p q M
                      ↝↝
                      coerce p q N

    -- COERCION RULES

    coerce-return   : {X : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'} → 
                      (V : Γ ⊢V⦂ X) →
                      --------------------------------
                      coerce p q (return V) ↝↝ return V

    coerce-↑        : {X : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'}
                      {op : Σₛ} → 
                      (r : op ∈ₒ o) →
                      (V : Γ ⊢V⦂ ```(payload op)) →
                      (M : Γ ⊢M⦂ X ! (o , i)) →
                      -------------------------------
                      coerce p q (↑ op r V M)
                      ↝↝
                      ↑ op (p op r) V (coerce p q M)

    coerce-promise  : {X Y : VType}
                      {o o' o'' : O}
                      {i i' i'' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'}
                      {op : Σₛ} →
                      (r : just (o'' , i'') ⊑-aux lkpᵢ op i)
                      (s : (∅ᵢ [ op ↦ just (o'' , i'') ]ᵢ) ⊑ᵢ i'') →
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙 ! (o'' , i'')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                      ------------------------------------------------------------------
                      coerce p q (promise op ∣ r , s ↦ M `in N)
                      ↝↝
                      promise op ∣ (⊑-aux-trans _ _ _ r (rel q op)) , s ↦ M `in (coerce p q N)

    coerce-await   : {X Y : VType}
                     {o o' : O}
                     {i i' : I}
                     {p : o ⊑ₒ o'}
                     {q : i ⊑ᵢ i'} →
                     (V : Γ ⊢V⦂ ⟨ X ⟩) →
                     (M : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                     -----------------------------
                     coerce p q (await V until M)
                     ↝↝
                     await V until (coerce p q M)


-- ONE-TO-ONE CORRESPONDENCE BETWEEN THE TWO SETS OF REDUCTION RULES

↝↝-to-↝ : {Γ : Ctx}
          {C : CType}
          {M N : Γ ⊢M⦂ C} → 
          M ↝↝ N →
          -----------------
          M ↝ N

↝↝-to-↝ (apply M V) =
  apply M V
↝↝-to-↝ (let-return V N) =
  let-return V N
↝↝-to-↝ (let-↑ p V M N) =
  let-↑ p V M N
↝↝-to-↝ (let-promise p q M₁ M₂ N) =
  let-promise p q M₁ M₂ N
↝↝-to-↝ (let-await V M N) =
  let-await V M N
↝↝-to-↝ (promise-↑ p q r V M N) =
  promise-↑ p q r V M N
↝↝-to-↝ (↓-return V W) =
  ↓-return V W
↝↝-to-↝ (↓-↑ p V W M) =
  ↓-↑ p V W M
↝↝-to-↝ (↓-promise-op p q V M N) =
  ↓-promise-op p q V M N
↝↝-to-↝ (↓-promise-op' p q r V M N) =
  ↓-promise-op' p q r V M N
↝↝-to-↝ (↓-await V M N) =
  ↓-await V M N
↝↝-to-↝ (match+-inl V M N) =
  match+-inl V M N
↝↝-to-↝ (match+-inr V M N) =
  match+-inr V M N
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
↝↝-to-↝ (context-coerce r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (coerce-return V) =
  coerce-return V
↝↝-to-↝ (coerce-↑ p V M) =
  coerce-↑ p V M
↝↝-to-↝ (coerce-promise p q M N) =
  coerce-promise p q M N
↝↝-to-↝ (coerce-await V M) =
  coerce-await V M


mutual
  ↝-context-to-↝↝ : {Γ : Ctx}
                    {Δ : BCtx}
                    {C : CType} → 
                    (E : Γ ⊢E[ Δ ]⦂ C) → 
                    {M N : (Γ ⋈ Δ) ⊢M⦂ hole-ty-e E} → 
                    M ↝ N →
                    ---------------------------
                    E [ M ] ↝↝ E [ N ]

  ↝-context-to-↝↝ [-] r =
    ↝-to-↝↝ r
  ↝-context-to-↝↝ (let= E `in x) r =
    context-let (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (↑ op p V E) r =
    context-↑ (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (↓ op V E) r =
    context-↓ (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (promise op ∣ p , q ↦ M `in E) r =
    context-promise (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (coerce p q E) r =
    context-coerce (↝-context-to-↝↝ E r)
  
 
  ↝-to-↝↝ : {Γ : Ctx}
            {C : CType}
            {M N : Γ ⊢M⦂ C} → 
            M ↝ N →
            -----------------
            M ↝↝ N

  ↝-to-↝↝ (apply M V) =
    apply M V
  ↝-to-↝↝ (let-return V N) =
    let-return V N
  ↝-to-↝↝ (let-↑ p V M N) =
    let-↑ p V M N
  ↝-to-↝↝ (let-promise p q M₁ M₂ N) =
    let-promise p q M₁ M₂ N
  ↝-to-↝↝ (let-await V M N) =
    let-await V M N
  ↝-to-↝↝ (promise-↑ p q r V M N) =
    promise-↑ p q r V M N
  ↝-to-↝↝ (↓-return V W) =
    ↓-return V W
  ↝-to-↝↝ (↓-↑ p V W M) =
    ↓-↑ p V W M
  ↝-to-↝↝ (↓-promise-op p q V M N) =
    ↓-promise-op p q V M N
  ↝-to-↝↝ (↓-promise-op' p q r V M N) =
    ↓-promise-op' p q r V M N
  ↝-to-↝↝ (↓-await V M N) =
    ↓-await V M N
  ↝-to-↝↝ (match+-inl V M N) =
    match+-inl V M N
  ↝-to-↝↝ (match+-inr V M N) =
    match+-inr V M N
  ↝-to-↝↝ (await-promise V M) =
    await-promise V M
  ↝-to-↝↝ (context E r) =
    ↝-context-to-↝↝ E r
  ↝-to-↝↝ (coerce-return V) =
    coerce-return V
  ↝-to-↝↝ (coerce-↑ r V M) =
    coerce-↑ r V M
  ↝-to-↝↝ (coerce-promise r s M N) =
    coerce-promise r s M N
  ↝-to-↝↝ (coerce-await V M) =
    coerce-await V M


-- FINALITY OF RESULT FORMS


run-finality-↝↝ : {Γ : Ctx}
                  {C : CType}
                  {M N : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
                  RunResult⟨ Γ ∣ M ⟩ →
                  M ↝↝ N →
                  -----------------------
                  ⊥

run-finality-↝↝ (promise R) (context-promise r) = run-finality-↝↝ R r


comp-finality-↝↝ : {Γ : Ctx}
                   {C : CType}
                   {M N : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
                   CompResult⟨ Γ ∣ M ⟩ →
                   M ↝↝ N →
                   -----------------------
                   ⊥

comp-finality-↝↝ (comp R) r =
  run-finality-↝↝ R r
comp-finality-↝↝ (signal R) (context-↑ r) =
  comp-finality-↝↝ R r


comp-finality : {Γ : Ctx}
                {C : CType}
                {M N : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
                CompResult⟨ Γ ∣ M ⟩ →
                M ↝ N →
                -----------------------
                ⊥

comp-finality R r =
  comp-finality-↝↝ R (↝-to-↝↝ r)