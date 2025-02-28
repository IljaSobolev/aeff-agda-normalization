open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Data.Maybe
open import Data.Product

open import AEff
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module Preservation where


-- BINDING CONTEXTS

BCtx = List Type


-- WELL-TYPED EVALUATION CONTEXTS

data _⊢E[_]⦂_ (Γ : Ctx) : (Δ : BCtx) → Type → Set where

  [-]              : {C : Type} → 
                     -------------
                     Γ ⊢E[ [] ]⦂ C

  let=_`in_        : {Δ : BCtx}
                     {X Y : Type} →
                     Γ ⊢E[ Δ ]⦂ X →
                     Γ ∷ X ⊢M⦂ Y →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ Y

  ↑                : {Δ : BCtx}
                     {X : Type}
                     (op : Σₛ) →
                     Γ ⊢V⦂ ``(payload op) →
                     Γ ⊢E[ Δ ]⦂ X →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ X

  ↓                : {Δ : BCtx}
                     {X : Type}
                     (op : Σₛ) →
                     Γ ⊢V⦂ ``(payload op) →
                     Γ ⊢E[ Δ ]⦂ X →
                     ---------------------------
                     Γ ⊢E[ Δ ]⦂ X

  promise_↦_`in_ : {Δ : BCtx}
                     {X Y : Type}
                     (op : Σₛ) →
                     Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ →
                     Γ ∷ ⟨ X ⟩ ⊢E[ Δ ]⦂ Y →
                     ------------------------------------------
                     Γ ⊢E[ X ∷ₗ Δ ]⦂ Y


-- MERGING AN ORDINARY CONTEXT AND A BINDING CONTEXT

infix 30 _⋈_

_⋈_ : Ctx → BCtx → Ctx
Γ ⋈ [] = Γ
Γ ⋈ (X ∷ₗ Δ) = (Γ ∷ ⟨ X ⟩) ⋈ Δ


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED EVALUATION CONTEXT

hole-ty-e : {Γ : Ctx} {Δ : BCtx} {C : Type} → Γ ⊢E[ Δ ]⦂ C → Type
hole-ty-e {_} {_} {C} [-] =
  C
hole-ty-e (let= E `in M) =
  hole-ty-e E
hole-ty-e (↑ op V E) =
  hole-ty-e E
hole-ty-e (↓ op V E) =
  hole-ty-e E
hole-ty-e (promise op ↦ M `in E) =
  hole-ty-e E


-- FILLING A WELL-TYPED EVALUATION CONTEXT

{- LEMMA 3.5 -}

infix 30 _[_]

_[_] : {Γ : Ctx} {Δ : BCtx} {C : Type} → (E : Γ ⊢E[ Δ ]⦂ C) → Γ ⋈ Δ ⊢M⦂ (hole-ty-e E) → Γ ⊢M⦂ C
[-] [ M ] =
  M
(let= E `in N) [ M ] =
  let= (E [ M ]) `in N
↑ op V E [ M ] =
  ↑ op V (E [ M ])
↓ op V E [ M ] =
  ↓ op V (E [ M ])
(promise op ↦ N `in E) [ M ] =
  promise op ↦ N `in (E [ M ])


-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-var : {Γ : Ctx} → (Δ : BCtx) → {A : BType} → `` A ∈ Γ ⋈ Δ → `` A ∈ Γ
strengthen-var [] x = x
strengthen-var (y ∷ₗ Δ) x with strengthen-var Δ x
... | Tl p = p


strengthen-val : {Γ : Ctx} {Δ : BCtx} {A : BType} → Γ ⋈ Δ ⊢V⦂ `` A → Γ ⊢V⦂ `` A
strengthen-val {_} {Δ} (` x) =
  ` strengthen-var Δ x
strengthen-val (``_ c) =
  ``_ c

strengthen-val-[] : {Γ : Ctx}
                    {A : BType} → 
                    (V : Γ ⋈ [] ⊢V⦂ `` A) →
                    --------------------
                    strengthen-val {Δ = []} V ≡ V

strengthen-val-[] (` x) =
  refl
strengthen-val-[] (``_ c) =
  refl


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

{- THEOREM 3.6 -}

infix 10 _↝_

data _↝_ {Γ : Ctx} : {C : Type} → Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

  -- COMPUTATIONAL RULES

  apply           : {X : Type}
                    {C : Type} →
                    (M : Γ ∷ X ⊢M⦂ C) →
                    (V : Γ ⊢V⦂ X) →
                    ----------------------
                    (ƛ M) · V
                    ↝
                    M [ id-subst [ V ]s ]m

  let-return      : {X Y : Type}
                    (V : Γ ⊢V⦂ X) →
                    (N : Γ ∷ X ⊢M⦂ Y) →
                    -----------------------------
                    let= (return V) `in N
                    ↝
                    N [ id-subst [ V ]s ]m

  let-↑           : {X Y : Type}
                    {op : Σₛ} →
                    (V : Γ ⊢V⦂ ``(payload op)) →
                    (M : Γ ⊢M⦂ X) →
                    (N : Γ ∷ X ⊢M⦂ Y) →
                    -----------------------------
                    let= (↑ op V M) `in N
                    ↝
                    ↑ op V (let= M `in N)

  let-promise     : {X Y Z : Type}
                    {op : Σₛ} →
                    (M₁ : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩) →
                    (M₂ : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    (N : Γ ∷ Y ⊢M⦂ Z) →
                    ---------------------------------------------------------------------------
                    let= (promise op ↦ M₁ `in M₂) `in N
                    ↝
                    (promise op ↦ M₁ `in (let= M₂ `in (M-rename (comp-ren exchange wk₁) N)))

  promise-↑       : {X Y : Type}
                    {op op' : Σₛ} →
                    (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``(payload op')) → 
                    (M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    --------------------------------------------
                    (promise op ↦ M `in (↑ op' V N))
                    ↝
                    ↑ op' (strengthen-val {Δ = X ∷ₗ []} V) (promise op ↦ M `in N)

  ↓-return        : {X : Type}
                    {op : Σₛ} →
                    (V : Γ ⊢V⦂ ``(payload op)) →
                    (W : Γ ⊢V⦂ X) →
                    ----------------------------------------------------------------
                    ↓ op V (return W)
                    ↝
                    return W

  ↓-↑             : {X : Type}
                    {op : Σₛ}
                    {op' : Σₛ} →
                    (V : Γ ⊢V⦂ ``(payload op)) →
                    (W : Γ ⊢V⦂ ``(payload op')) →
                    (M : Γ ⊢M⦂ X) →
                    -------------------------------
                    ↓ op V (↑ op' W M)
                    ↝
                    ↑ op' W (↓ op V M)

  ↓-promise-op    : {X Y : Type}
                    {op : Σₛ} →
                    (V : Γ ⊢V⦂ ``(payload op)) → 
                    (M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    ---------------------------------------------------------------------------------------
                    ↓ op V (promise op ↦ M `in N )
                    ↝
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
                    ↝
                    promise op' ↦ M `in (↓ op (V-rename wk₁ V) N)

  await-promise   : {X : Type}
                    {C : Type} → 
                    (V : Γ ⊢V⦂ X) → 
                    (M : Γ ∷ X ⊢M⦂ C) →
                    --------------------
                    await ⟨ V ⟩ until M
                    ↝
                    M [ id-subst [ V ]s ]m

  -- EVALUATION CONTEXT RULE

  context         : {Δ : BCtx}
                    {C : Type} → 
                    (E : Γ ⊢E[ Δ ]⦂ C) →
                    {M N : Γ ⋈ Δ ⊢M⦂ (hole-ty-e E)} →
                    M ↝ N →
                    -------------------------------
                    E [ M ] ↝ E [ N ]