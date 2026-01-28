{-# OPTIONS --guardedness #-}

open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Data.Maybe
open import Data.Product

open import AEffReinstSN.AEff
open import AEffReinstSN.CoinductiveEffectAnnotations
open import AEffReinstSN.Renamings
open import AEffReinstSN.Substitutions
open import AEffReinstSN.Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module AEffReinstSN.Preservation where


-- BINDING CONTEXTS

BCtx = List VType


-- WELL-TYPED EVALUATION CONTEXTS

data _⊢E[_]⦂_ (Γ : Ctx) : (Δ : BCtx) → CType → Set where

  [-]                : {C : CType} → 
                       -------------
                       Γ ⊢E[ [] ]⦂ C

  let=_`in_          : {Δ : BCtx}
                       {X Y : VType}
                       {o : O}
                       {i : I} →
                       Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                       Γ ∷ X ⊢M⦂ Y ! (o , i) →
                       ------------------------
                       Γ ⊢E[ Δ ]⦂ Y ! (o , i)

  ↑                  : {Δ : BCtx}
                       {X : VType}
                       {o : O}
                       {i : I} →
                       (op : Σₛ) →
                       op ∈ₒ o →
                       Γ ⊢V⦂ ```(payload op) →
                       Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                       ------------------------
                       Γ ⊢E[ Δ ]⦂ X ! (o , i)

  ↓                  : {Δ : BCtx}
                       {X : VType}
                       {o : O}
                       {i : I}
                       (op : Σₛ) →
                       Γ ⊢V⦂ ```(payload op) →
                       Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                       ---------------------------
                       Γ ⊢E[ Δ ]⦂ X ! op ↓ₑ (o , i)

  promise_∣_,_↦_`in_ : {Δ : BCtx}
                       {X Y : VType}
                       {o o' : O}
                       {i i' : I} → 
                       (op : Σₛ) →
                       just (o' , i') ⊑-aux lkpᵢ op i →
                       (∅ᵢ [ op ↦ just (o' , i') ]ᵢ) ⊑ᵢ i' →
                       Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙 ! (o' , i') →
                       Γ ∷ ⟨ X ⟩ ⊢E[ Δ ]⦂ Y ! (o , i) →
                       ------------------------------------------
                       Γ ⊢E[ X ∷ₗ Δ ]⦂ Y ! (o , i)

  coerce             : {Δ : BCtx}
                       {X : VType}
                       {o o' : O}
                       {i i' : I} →
                       o ⊑ₒ o' →
                       i ⊑ᵢ i' → 
                       Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                       ------------------------
                       Γ ⊢E[ Δ ]⦂ X ! (o' , i')


-- MERGING AN ORDINARY CONTEXT AND A BINDING CONTEXT

infix 30 _⋈_

_⋈_ : Ctx → BCtx → Ctx
Γ ⋈ [] = Γ
Γ ⋈ (X ∷ₗ Δ) = (Γ ∷ ⟨ X ⟩) ⋈ Δ


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED EVALUATION CONTEXT

hole-ty-e : {Γ : Ctx} {Δ : BCtx} {C : CType} → Γ ⊢E[ Δ ]⦂ C → CType
hole-ty-e {_} {_} {C} [-] =
  C
hole-ty-e (let= E `in M) =
  hole-ty-e E
hole-ty-e (↑ op p V E) =
  hole-ty-e E
hole-ty-e (↓ op V E) =
  hole-ty-e E
hole-ty-e (promise op ∣ p , q ↦ M `in E) =
  hole-ty-e E
hole-ty-e (coerce p q E) =
  hole-ty-e E


-- FILLING A WELL-TYPED EVALUATION CONTEXT

infix 30 _[_]

_[_] : {Γ : Ctx} {Δ : BCtx} {C : CType} → (E : Γ ⊢E[ Δ ]⦂ C) → Γ ⋈ Δ ⊢M⦂ (hole-ty-e E) → Γ ⊢M⦂ C
[-] [ M ] =
  M
(let= E `in N) [ M ] =
  let= (E [ M ]) `in N
↑ op p V E [ M ] =
  ↑ op p V (E [ M ])
↓ op V E [ M ] =
  ↓ op V (E [ M ])
(promise op ∣ p , q ↦ N `in E) [ M ] =
  promise op ∣ p , q ↦ N `in (E [ M ])
coerce p q E [ M ] =
  coerce p q (E [ M ])


-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-var : {Γ : Ctx} → (Δ : BCtx) → {A : BType} → ``` A ∈ Γ ⋈ Δ → ``` A ∈ Γ
strengthen-var [] x = x
strengthen-var (y ∷ₗ Δ) x with strengthen-var Δ x
... | Tl p = p


strengthen-val : {Γ : Ctx} {Δ : BCtx} {A : BType} → Γ ⋈ Δ ⊢V⦂ ``` A → Γ ⊢V⦂ ``` A
strengthen-val {_} {Δ} (` x) =
  ` strengthen-var Δ x
strengthen-val (``_ c) =
  ``_ c

strengthen-val-[] : {Γ : Ctx}
                    {A : BType} → 
                    (V : Γ ⋈ [] ⊢V⦂ ``` A) →
                    --------------------
                    strengthen-val {Δ = []} V ≡ V

strengthen-val-[] (` x) =
  refl
strengthen-val-[] (``_ c) =
  refl


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

infix 10 _↝_

data _↝_ {Γ : Ctx} : {C : CType} → Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

  -- COMPUTATIONAL RULES

  apply           : {X : VType}
                    {C : CType} →
                    (M : Γ ∷ X ⊢M⦂ C) →
                    (V : Γ ⊢V⦂ X) →
                    ----------------------
                    (ƛ M) · V
                    ↝
                    M [ id-subst [ V ]s ]m

  let-return      : {X Y : VType}
                    {o : O}
                    {i : I} → 
                    (V : Γ ⊢V⦂ X) →
                    (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                    -----------------------------
                    let= (return V) `in N
                    ↝
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
                    ↝
                    ↑ op p V (let= M `in N)

  let-promise     : {X Y Z : VType}
                    {o o' : O}
                    {i i' : I}
                    {op : Σₛ} →
                    (p : just (o' , i') ⊑-aux lkpᵢ op i ) →
                    (q : (∅ᵢ [ op ↦ just (o' , i') ]ᵢ) ⊑ᵢ i') →
                    (M₁ : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙 ! (o' , i')) →
                    (M₂ : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                    (N : Γ ∷ Y ⊢M⦂ Z ! (o , i)) →
                    ---------------------------------------------------------------------------
                    let= (promise op ∣ p , q ↦ M₁ `in M₂) `in N
                    ↝
                    (promise op ∣ p , q ↦ M₁ `in (let= M₂ `in (M-rename (wk₂ wk₁) N)))

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
                    ↝
                    ↑ op' r (strengthen-val {Δ = X ∷ₗ []} V) (promise op ∣ p , q ↦ M `in N)

  ↓-return        : {X : VType}
                    {o : O}
                    {i : I}
                    {op : Σₛ} →
                    (V : Γ ⊢V⦂ ```(payload op)) →
                    (W : Γ ⊢V⦂ X) →
                    ----------------------------------------------------------------
                    ↓ {o = o} {i = i} op V (return W)
                    ↝
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
                    ↝
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
                    ↓ op V (promise op ∣ p , q ↦ M `in N )
                    ↝
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
                    ↝
                    promise op' ∣ ⊑-aux-trans _ _ _ q (lkpᵢ-↓ₑ-neq-⊑ {i = i} {o = o} p) , r ↦ M `in (↓ op (V-rename wk₁ V) N)

  match+-inl      : {X Y : VType}
                    {C : CType}
                    (V : Γ ⊢V⦂ X)
                    (M : Γ ∷ X ⊢M⦂ C)
                    (N : Γ ∷ Y ⊢M⦂ C) →
                    ------------------
                    match+ (inl V) M N
                    ↝
                    M [ id-subst [ V ]s ]m

  match+-inr      : {X Y : VType}
                    {C : CType}
                    (V : Γ ⊢V⦂ Y)
                    (M : Γ ∷ X ⊢M⦂ C)
                    (N : Γ ∷ Y ⊢M⦂ C) →
                    ------------------
                    match+ (inr V) M N
                    ↝
                    N [ id-subst [ V ]s ]m

  await-promise   : {X : VType}
                    {C : CType} → 
                    (V : Γ ⊢V⦂ X) → 
                    (M : Γ ∷ X ⊢M⦂ C) →
                    --------------------
                    await ⟨ V ⟩ until M
                    ↝
                    M [ id-subst [ V ]s ]m

  -- EVALUATION CONTEXT RULE

  context         : {Δ : BCtx}
                    {C : CType} → 
                    (E : Γ ⊢E[ Δ ]⦂ C) →
                    {M N : Γ ⋈ Δ ⊢M⦂ (hole-ty-e E)} →
                    M ↝ N →
                    -------------------------------
                    E [ M ] ↝ E [ N ]

  -- COERCION RULES
  -- (THE RESULT OF WORKING WITH WELL-TYPED SYNTAX AND MAKING SUBSUMPTION INTO AN EXPLICIT COERCION)

  coerce-return   : {X : VType}
                    {o o' : O}
                    {i i' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'} → 
                    (V : Γ ⊢V⦂ X) →
                    --------------------------------
                    coerce p q (return V) ↝ return V

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
                    ↝
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
                    ↝
                    promise op ∣ (⊑-aux-trans _ _ _ r (rel q op)) , s ↦ M `in (coerce p q N)