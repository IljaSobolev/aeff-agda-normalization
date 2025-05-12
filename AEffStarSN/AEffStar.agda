open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.List using (List; []) renaming (_∷_ to _∷ₗ_)

open import EffectAnnotations using (Σₛ; decₛ)
open import AEff using (payload; Σ-base; ar-base)
open import Types using (BType; dec-bty; GType)

module AEffStarSN.AEffStar where

-- VALUE AND COMPUTATION TYPES

mutual

  data Type : Set where
    ```  : GType → Type
    _⇒_  : Type → Type → Type
    ⟨_⟩  : Type → Type

infix 30 _⇒_


-- SNOC LISTS FOR MODELLING CONTEXTS

infixl 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A


-- CONTEXTS AND VARIABLES IN THEM (I.E., DE BRUIJN INDICES)

Ctx = SnocList Type

data _∈_ (X : Type) : Ctx → Set where
  Hd : {Γ : Ctx} → X ∈ (Γ ∷ X)
  Tl : {Γ : Ctx} {Y : Type} → X ∈ Γ → X ∈ (Γ ∷ Y)


-- DERIVATIONS OF WELL-TYPED TERMS

mutual

  data _⊢V⦂_ (Γ : Ctx) : Type → Set where
  
    `_  : {X : Type} →
          X ∈ Γ →
          -------------
          Γ ⊢V⦂ X
          
    ``_  : (c : Σ-base) →
          --------------
          Γ ⊢V⦂ ```(ar-base c)
          
    ƛ   : {X : Type}
          {C : Type} →
          Γ ∷ X ⊢M⦂ C → 
          -------------
          Γ ⊢V⦂ X ⇒ C

    ⟨_⟩ : {X : Type} →
          Γ ⊢V⦂ X →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩

    ★   : {X : Type} →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩
          
          
  infix 40 _·_

  data _⊢M⦂_ (Γ : Ctx) : Type → Set where

    return          : {X : Type} →
                      Γ ⊢V⦂ X →
                      -----------------
                      Γ ⊢M⦂ X

    let=_`in_       : {X Y : Type} →
                      Γ ⊢M⦂ X →
                      Γ ∷ X ⊢M⦂ Y →
                      -----------------------
                      Γ ⊢M⦂ Y

    _·_             : {X : Type}
                      {C : Type} → 
                      Γ ⊢V⦂ X ⇒ C →
                      Γ ⊢V⦂ X →
                      -------------
                      Γ ⊢M⦂ C

    ↑               : {X : Type}
                      (op : Σₛ) →
                      Γ ⊢V⦂ ```(payload op) →
                      Γ ⊢M⦂ X →
                      ----------------------
                      Γ ⊢M⦂ X

    ↓               : {X : Type}
                      (op : Σₛ) →
                      Γ ⊢V⦂ ```(payload op) →
                      Γ ⊢M⦂ X →
                      ----------------------
                      Γ ⊢M⦂ X

    promise_↦_`in_ : {X Y : Type}
                       (op : Σₛ) →
                       Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ →
                       Γ ∷ ⟨ X ⟩ ⊢M⦂ Y →
                       ------------------------------------------
                       Γ ⊢M⦂ Y

    await_until_    : {X : Type}
                      {C : Type} → 
                      Γ ⊢V⦂ ⟨ X ⟩ →
                      Γ ∷ X ⊢M⦂ C →
                      --------------
                      Γ ⊢M⦂ C

    coerce          : {X : Type} →
                      Γ ⊢M⦂ X →
                      ------------
                      Γ ⊢M⦂ X



-- SET OF RENAMINGS BETWEEN CONTEXTS

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : Type} → X ∈ Γ → X ∈ Γ'


-- IDENTITY, COMPOSITION, AND EXCHANGE RENAMINGS

id-ren : {Γ : Ctx} → Ren Γ Γ 
id-ren {X} x = x


comp-ren : {Γ Γ' Γ'' : Ctx} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ'' 
comp-ren f g x = f (g x)


exchange : {Γ : Ctx} {X Y : Type} → Ren (Γ ∷ X ∷ Y) (Γ ∷ Y ∷ X)
exchange Hd = Tl Hd
exchange (Tl Hd) = Hd
exchange (Tl (Tl x)) = Tl (Tl x)


-- WEAKENING OF RENAMINGS

wk₁ : {Γ : Ctx} {X : Type} → Ren Γ (Γ ∷ X)
wk₁ = Tl


wk₂ : {Γ Γ' : Ctx} {X : Type} → Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
wk₂ f Hd = Hd
wk₂ f (Tl v) = Tl (f v)


wk₃ : {Γ : Ctx} {X Y Z : Type} → Ren (Γ ∷ Y ∷ Z) (Γ ∷ X ∷ Y ∷ Z)
wk₃ Hd = Hd
wk₃ (Tl Hd) = Tl Hd
wk₃ (Tl (Tl x)) = Tl (Tl (Tl x))


-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  V-rename : {X : Type} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X
  V-rename f (` x) = ` f x
  V-rename f (`` c) = `` c
  V-rename f (ƛ M) = ƛ (M-rename (wk₂ f) M)
  V-rename f ⟨ V ⟩ = ⟨ V-rename f V ⟩
  V-rename f ★ = ★

  M-rename : {C : Type} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢M⦂ C → Γ' ⊢M⦂ C
  M-rename f (return V) =
    return (V-rename f V)
  M-rename f (let= M `in N) =
    let= M-rename f M `in M-rename (wk₂ f) N
  M-rename f (V · W) =
    V-rename f V · V-rename f W
  M-rename f (↑ op V M) =
    ↑ op (V-rename f V) (M-rename f M)
  M-rename f (↓ op V M) =
    ↓ op (V-rename f V) (M-rename f M)
  M-rename f (promise op ↦ M `in N) =
    promise op ↦ M-rename (wk₂ f) M `in M-rename (wk₂ f) N
  M-rename f (await V until M) =
    await (V-rename f V) until (M-rename (wk₂ f) M)
  M-rename f (coerce M) =
    coerce (M-rename f M)


-- SET OF SUBSTITUTIONS BETWEEN CONTEXTS

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : Type} → X ∈ Γ → Γ' ⊢V⦂ X


-- IDENTITY AND EXTENSION SUBSTITUTIONS

id-subst : {Γ : Ctx} → Sub Γ Γ
id-subst x = ` x

_[_]s : {Γ Γ' : Ctx} {X : Type} → Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl x) = s x


-- LIFTING SUBSTITUTIONS

lift : {Γ Γ' : Ctx} {X : Type} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)


-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  infix 40 _[_]v
  infix 40 _[_]m

  _[_]v : {Γ Γ' : Ctx} → {X : Type} → Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X
  (` x) [ s ]v =
    s x
  (`` c) [ s ]v =
    `` c
  (ƛ M) [ s ]v =
    ƛ (M [ lift s ]m)
  ⟨ V ⟩ [ s ]v =
    ⟨ V [ s ]v ⟩
  ★ [ s ]v =
    ★

  _[_]m : {Γ Γ' : Ctx} → {C : Type} → Γ ⊢M⦂ C → Sub Γ Γ'  → Γ' ⊢M⦂ C
  (return V) [ s ]m =
    return (V [ s ]v)
  (let= M `in N) [ s ]m =
    let= (M [ s ]m) `in (N [ lift s ]m)
  (V · W) [ s ]m =
    (V [ s ]v) · (W [ s ]v)
  (↑ op V M) [ s ]m =
    ↑ op (V [ s ]v) (M [ s ]m)
  (↓ op V M) [ s ]m =
    ↓ op (V [ s ]v) (M [ s ]m)
  (promise op ↦ M `in N) [ s ]m =
    promise op ↦ (M [ lift s ]m) `in (N [ lift s ]m)
  (await V until M) [ s ]m =
    await (V [ s ]v) until (M [ lift s ]m)
  (coerce M) [ s ]m =
    coerce (M [ s ]m)


-- BINDING CONTEXTS

BCtx = List Type

-- MERGING AN ORDINARY CONTEXT AND A BINDING CONTEXT

infix 30 _⋈_

_⋈_ : Ctx → BCtx → Ctx
Γ ⋈ [] = Γ
Γ ⋈ (X ∷ₗ Δ) = (Γ ∷ ⟨ X ⟩) ⋈ Δ

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
                    (V : Γ ⊢V⦂ ```(payload op)) →
                    (M : Γ ⊢M⦂ X) →
                    (N : Γ ∷ X ⊢M⦂ Y) →
                    -----------------------------
                    let= (↑ op V M) `in N
                    ↝↝
                    ↑ op V (let= M `in N)

  let-promise     : {X Y Z : Type}
                    {op : Σₛ} →
                    (M₁ : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩) →
                    (M₂ : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    (N : Γ ∷ Y ⊢M⦂ Z) →
                    ---------------------------------------------------------------------------
                    let= (promise op ↦ M₁ `in M₂) `in N
                    ↝↝
                    (promise op ↦ M₁ `in (let= M₂ `in (M-rename (comp-ren exchange wk₁) N)))

  promise-↑       : {X Y : Type}
                    {op op' : Σₛ} →
                    (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op')) → 
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    --------------------------------------------
                    (promise op ↦ M `in (↑ op' V N))
                    ↝↝
                    ↑ op' (strengthen-val {Δ = X ∷ₗ []} V) (promise op ↦ M `in N)

  ↓-return        : {X : Type}
                    {op : Σₛ} →
                    (V : Γ ⊢V⦂ ```(payload op)) →
                    (W : Γ ⊢V⦂ X) →
                    ----------------------------------------------------------------
                    ↓ op V (return W)
                    ↝↝
                    return W

  ↓-↑             : {X : Type}
                    {op : Σₛ}
                    {op' : Σₛ} →
                    (V : Γ ⊢V⦂ ```(payload op)) →
                    (W : Γ ⊢V⦂ ```(payload op')) →
                    (M : Γ ⊢M⦂ X) →
                    -------------------------------
                    ↓ op V (↑ op' W M)
                    ↝↝
                    ↑ op' W (↓ op V M)


  ↓-promise-op    : {X Y : Type}
                    {op : Σₛ} →
                    (V : Γ ⊢V⦂ ```(payload op)) → 
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    ---------------------------------------------------------------------------------------
                    ↓ op V (promise op ↦ M `in N )
                    ↝↝
                    (let= (coerce (M [ id-subst [ V ]s ]m)) `in
                      ↓ op (V-rename wk₁ V) ((M-rename (comp-ren exchange wk₁) N) [ id-subst [ ` Hd ]s ]m))

  ↓-promise-op'   : {X Y : Type}
                    {op op' : Σₛ} →
                    (p : ¬ op ≡ op') →
                    (V : Γ ⊢V⦂ ```(payload op)) → 
                    (M : Γ ∷ ```(payload op') ⊢M⦂ ⟨ X ⟩) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    ------------------------------------------------------------------------------------------
                    ↓ op V (promise op' ↦ M `in N )
                    ↝↝
                    promise op' ↦ (coerce M) `in (↓ op (V-rename wk₁ V) N)

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
                     {V : Γ ⊢V⦂ ```(payload op)}
                     {M N : Γ ⊢M⦂ X} →
                     M ↝↝ N →
                     ---------------------------
                     ↑ op V M
                     ↝↝
                     ↑ op V N

  context-↓        : {X : Type}
                     {op : Σₛ}
                     {V : Γ ⊢V⦂ ```(payload op)}
                     {M N : Γ ⊢M⦂ X} →
                     M ↝↝ N →
                     ---------------------------
                     ↓ op V M
                     ↝↝
                     ↓ op V N

  context-promise : {X Y : Type}
                    {op : Σₛ} →
                    {M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩} →
                    {N N' : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y} →
                    N ↝↝ N' →
                    ------------------------------------------------
                    promise op ↦ M `in N
                    ↝↝
                    promise op ↦ M `in N'

  context-coerce  : {X : Type}
                    {M N : Γ ⊢M⦂ X} →
                    M ↝↝ N →
                    ---------------------------
                    coerce M
                    ↝↝
                    coerce N

  coerce-return   : {X : Type}
                    (V : Γ ⊢V⦂ X) →
                    --------------------------------
                    coerce (return V) ↝↝ return V

  coerce-↑        : {X : Type}
                    {op : Σₛ} →
                    (V : Γ ⊢V⦂ ```(payload op)) →
                    (M : Γ ⊢M⦂ X) →
                    -------------------------------
                    coerce (↑ op V M)
                    ↝↝
                    ↑ op V (coerce M)

  coerce-promise  : {X Y : Type}
                    {op : Σₛ} →
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    --------------------------------------
                    coerce (promise op ↦ M `in N)
                    ↝↝
                    promise op ↦ (coerce M) `in (coerce N)