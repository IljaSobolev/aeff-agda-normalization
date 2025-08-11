open import Data.List using (List; []) renaming (_∷_ to _∷ₗ_)

open import EffectAnnotations using (Σₛ)
open import AEff using (payload; Σ-base; ar-base)
open import Types using (BType; GType)

module AEffStarSN.AEffStar where

-- VALUE AND COMPUTATION TYPES

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

data _⊢V⦂_ (Γ : Ctx) : Type → Set

data _⊢M⦂_ (Γ : Ctx) (C : Type) : Set

data _⊢T⦂_⊸_ (Γ : Ctx) (X : Type) : Type → Set

data _⊢V⦂_ Γ where

  `_  : {X : Type} →
        X ∈ Γ →
        -------------
        Γ ⊢V⦂ X
        
  ``_ : (c : Σ-base) →
        --------------
        Γ ⊢V⦂ ```(ar-base c)
        
  ƛ   : {X C : Type} →
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

data _⊢M⦂_ Γ C where

  return         : Γ ⊢V⦂ C →
                   -------
                   Γ ⊢M⦂ C

  _·_            : {X : Type} →
                   Γ ⊢V⦂ X ⇒ C →
                   Γ ⊢V⦂ X →
                   -------
                   Γ ⊢M⦂ C

  ↑              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ⊢M⦂ C →
                   -------
                   Γ ⊢M⦂ C

  promise_↦_`in_ : {X : Type}
                   (op : Σₛ) →
                   Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ →
                   Γ ∷ ⟨ X ⟩ ⊢M⦂ C →
                   -------
                   Γ ⊢M⦂ C

  await_until_   : {X : Type} →
                   Γ ⊢V⦂ ⟨ X ⟩ →
                   Γ ∷ X ⊢M⦂ C →
                   -------
                   Γ ⊢M⦂ C

  _aT_           : {X : Type} →
                   Γ ⊢T⦂ X ⊸ C →
                   Γ ⊢M⦂ X →
                   -------
                   Γ ⊢M⦂ C

data _⊢T⦂_⊸_ Γ X where

  Tl : {Y : Type} →
       Γ ∷ X ⊢M⦂ Y →
       -----------
       Γ ⊢T⦂ X ⊸ Y

  T↓ : (op : Σₛ) →
       Γ ⊢V⦂ ```(payload op) →
       -----------
       Γ ⊢T⦂ X ⊸ X

  Tc : -----------
       Γ ⊢T⦂ X ⊸ X

pattern let=_`in_ M N = Tl N aT M
pattern ↓ op V M = T↓ op V aT M
pattern coerce M = Tc aT M

-- SET OF RENAMINGS BETWEEN CONTEXTS

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : Type} → X ∈ Γ → X ∈ Γ'

-- IDENTITY, COMPOSITION, AND EXCHANGE RENAMINGS

idr : {Γ : Ctx} → Ren Γ Γ 
idr {X} x = x

-- WEAKENING OF RENAMINGS

wk₁ : {Γ : Ctx} {X : Type} → Ren Γ (Γ ∷ X)
wk₁ = Tl

wk₂ : {Γ Γ' : Ctx} {X : Type} → Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
wk₂ f Hd = Hd
wk₂ f (Tl v) = Tl (f v)

-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

V-rename : {X : Type} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X
M-rename : {C : Type} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢M⦂ C → Γ' ⊢M⦂ C
T-rename : {X Y : Type} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢T⦂ X ⊸ Y → Γ' ⊢T⦂ X ⊸ Y

V-rename f (` x) =
  ` f x
V-rename f (`` c) =
  `` c
V-rename f (ƛ M) =
  ƛ (M-rename (wk₂ f) M)
V-rename f ⟨ V ⟩ =
  ⟨ V-rename f V ⟩
V-rename f ★ =
  ★

M-rename f (return V) =
  return (V-rename f V)
M-rename f (V · W) =
  V-rename f V · V-rename f W
M-rename f (↑ op V M) =
  ↑ op (V-rename f V) (M-rename f M)
M-rename f (promise op ↦ M `in N) =
  promise op ↦ M-rename (wk₂ f) M `in M-rename (wk₂ f) N
M-rename f (await V until M) =
  await (V-rename f V) until (M-rename (wk₂ f) M)
M-rename f (T aT M) =
  (T-rename f T) aT (M-rename f M)

T-rename f (Tl N) =
  Tl (M-rename (wk₂ f) N)
T-rename f (T↓ op V) =
  T↓ op (V-rename f V)
T-rename f Tc =
  Tc

-- SET OF SUBSTITUTIONS BETWEEN CONTEXTS

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : Type} → X ∈ Γ → Γ' ⊢V⦂ X

-- IDENTITY AND EXTENSION SUBSTITUTIONS

ids : {Γ : Ctx} → Sub Γ Γ
ids x = ` x

_[_]s : {Γ Γ' : Ctx} {X : Type} → Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl x) = s x

-- LIFTING SUBSTITUTIONS

lift : {Γ Γ' : Ctx} {X : Type} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)

-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

infix 40 _[_]v
infix 40 _[_]m

_[_]v : {Γ Γ' : Ctx} → {X : Type} → Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X
_[_]m : {Γ Γ' : Ctx} → {C : Type} → Γ ⊢M⦂ C → Sub Γ Γ' → Γ' ⊢M⦂ C
_[_]t : {Γ Γ' : Ctx} → {X Y : Type} → Γ ⊢T⦂ X ⊸ Y → Sub Γ Γ' → Γ' ⊢T⦂ X ⊸ Y

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

(return V) [ s ]m =
  return (V [ s ]v)
(V · W) [ s ]m =
  (V [ s ]v) · (W [ s ]v)
(↑ op V M) [ s ]m =
  ↑ op (V [ s ]v) (M [ s ]m)
(promise op ↦ M `in N) [ s ]m =
  promise op ↦ (M [ lift s ]m) `in (N [ lift s ]m)
(await V until M) [ s ]m =
  await (V [ s ]v) until (M [ lift s ]m)
(T aT M) [ s ]m =
  (T [ s ]t) aT (M [ s ]m)

Tl N [ s ]t =
  Tl (N [ lift s ]m)
T↓ op V [ s ]t =
  T↓ op (V [ s ]v)
Tc [ s ]t =
  Tc

-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-val : {Γ : Ctx} (X : Type) {A : BType} → Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A → Γ ⊢V⦂ ``` A
strengthen-val _ (` Tl x) = ` x
strengthen-val _ (`` c) = `` c

-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- WITH INLINED EVALUATION CONTEXT RULES

infix 10 _↝_

data _↝_ {Γ : Ctx} {C : Type} : Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

  -- COMPUTATIONAL RULES

  apply           : {X : Type}
                    (M : Γ ∷ X ⊢M⦂ C)
                    (V : Γ ⊢V⦂ X) →
                    ------------
                    ƛ M · V
                    ↝
                    M [ ids [ V ]s ]m

  let-return      : {X : Type}
                    (V : Γ ⊢V⦂ X)
                    (N : Γ ∷ X ⊢M⦂ C) →
                    ----------------
                    let= return V `in N
                    ↝
                    N [ ids [ V ]s ]m

  T-↑             : {X : Type}
                    {op : Σₛ}
                    (T : Γ ⊢T⦂ X ⊸ C)
                    (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ⊢M⦂ X) →
                    ------------
                    T aT (↑ op V M)
                    ↝
                    ↑ op V (T aT M)

  T-promise       : {X Y : Type}
                    {op : Σₛ}
                    (T : Γ ⊢T⦂ Y ⊸ C)
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    --------------------------
                    T aT (promise op ↦ M `in N)
                    ↝
                    (promise op ↦ M `in (T-rename wk₁ T aT N))

  T-await         : {X Y : Type}
                    (T : Γ ⊢T⦂ Y ⊸ C) 
                    (V : Γ ⊢V⦂ ⟨ X ⟩)
                    (M : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    T aT (await V until M)
                    ↝
                    await V until ((T-rename wk₁ T) aT M)

  promise-↑       : {X : Type}
                    {op op' : Σₛ}
                    (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op'))
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ C) →
                    --------------------
                    promise op ↦ M `in (↑ op' V N)
                    ↝
                    ↑ op' (strengthen-val X V) (promise op ↦ M `in N)

  ↓-return        : {op : Σₛ}
                    (V : Γ ⊢V⦂ ```(payload op))
                    (W : Γ ⊢V⦂ C) →
                    ------------
                    ↓ op V (return W)
                    ↝
                    return W

  ↓-promise-op    : {X : Type}
                    {op : Σₛ}
                    (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ C) →
                    --------------------
                    ↓ op V (promise op ↦ M `in N)
                    ↝
                    let= coerce (M [ ids [ V ]s ]m) `in (↓ op (V-rename wk₁ V) N)

  await-promise   : {X : Type}
                    (V : Γ ⊢V⦂ X)
                    (M : Γ ∷ X ⊢M⦂ C) →
                    ----------------
                    await ⟨ V ⟩ until M
                    ↝
                    M [ ids [ V ]s ]m

  ↑-discard       : {M : Γ ⊢M⦂ C}
                    {op : Σₛ} (V : Γ ⊢V⦂ ```(payload op)) →
                    --------
                    ↑ op V M
                    ↝
                    M

  -- INLINED EVALUATION CONTEXT RULES

  context-↑       : {op : Σₛ}
                    {V : Γ ⊢V⦂ ```(payload op)}
                    {M N : Γ ⊢M⦂ C} →
                    M ↝ N →
                    -----
                    ↑ op V M
                    ↝
                    ↑ op V N

  context-promise : {X : Type}
                    {op : Σₛ}
                    {M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩}
                    {N N' : Γ ∷ ⟨ X ⟩ ⊢M⦂ C} →
                    N ↝ N' →
                    -----
                    promise op ↦ M `in N
                    ↝
                    promise op ↦ M `in N'

  context-T       : {X : Type}
                    {M N : Γ ⊢M⦂ X}
                    (T : Γ ⊢T⦂ X ⊸ C) →
                    M ↝ N →
                    -----
                    T aT M
                    ↝
                    T aT N

  coerce-return   : (V : Γ ⊢V⦂ C) →
                    ------------
                    coerce (return V)
                    ↝
                    return V