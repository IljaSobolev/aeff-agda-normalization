open import Data.List using (List; []) renaming (_∷_ to _∷ₗ_)

open import EffectAnnotations using (Σₛ)
open import AEff using (payload; Σ-base; ar-base)
open import Types using (BType; GType)

module AEffStarSN.AEffStar where

variable
  A : BType
  op op' : Σₛ

-- VALUE AND COMPUTATION TYPES

infix 30 _⇒_

data Type : Set where
  ```  : GType → Type
  _⇒_  : Type → Type → Type
  ⟨_⟩  : Type → Type

variable
  X Y Z U : Type

-- SNOC LISTS FOR MODELLING CONTEXTS

infixl 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A

-- CONTEXTS AND VARIABLES IN THEM (I.E., DE BRUIJN INDICES)

Ctx = SnocList Type

variable
  Γ Γ' Γ'' Δ Δ' : Ctx

data _∈_ (X : Type) : Ctx → Set where
  Hd : X ∈ (Γ ∷ X)
  Tl : X ∈ Γ → X ∈ (Γ ∷ Y)

variable
  x : X ∈ Γ

-- DERIVATIONS OF WELL-TYPED TERMS

data _⊢V⦂_ (Γ : Ctx) : Type → Set

data _⊢M⦂_ (Γ : Ctx) (Y : Type) : Set

data _⊢T⦂_⊸_ (Γ : Ctx) (X : Type) : Type → Set

data _⊢V⦂_ Γ where
  `_  : X ∈ Γ → Γ ⊢V⦂ X
  ``_ : (c : Σ-base) → Γ ⊢V⦂ ```(ar-base c)
  ƛ   : Γ ∷ X ⊢M⦂ Y → Γ ⊢V⦂ X ⇒ Y
  ⟨_⟩ : Γ ⊢V⦂ X → Γ ⊢V⦂ ⟨ X ⟩

infix 40 _·_

data _⊢M⦂_ Γ Y where

  return         : Γ ⊢V⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  _·_            : Γ ⊢V⦂ X ⇒ Y →
                   Γ ⊢V⦂ X →
                   -------
                   Γ ⊢M⦂ Y

  ↑              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  promise_↦_`in_ : (op : Σₛ) →
                   Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ →
                   Γ ∷ ⟨ X ⟩ ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  await_until_   : Γ ⊢V⦂ ⟨ X ⟩ →
                   Γ ∷ X ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  _aT_           : Γ ⊢T⦂ X ⊸ Y →
                   Γ ⊢M⦂ X →
                   -------
                   Γ ⊢M⦂ Y

data _⊢T⦂_⊸_ Γ X where

  Tl : Γ ∷ X ⊢M⦂ Y →
       -----------
       Γ ⊢T⦂ X ⊸ Y

  T↓ : (op : Σₛ) →
       Γ ⊢V⦂ ```(payload op) →
       -----------
       Γ ⊢T⦂ X ⊸ X

  Tc : -----------
       Γ ⊢T⦂ X ⊸ X

variable
  V V' W W' : Γ ⊢V⦂ X
  M M' N N' L L' : Γ ⊢M⦂ X
  T T' : Γ ⊢T⦂ X ⊸ Y

pattern let=_`in_ M N = Tl N aT M
pattern ↓ op V M = T↓ op V aT M
pattern coerce M = Tc aT M

-- SET OF RENAMINGS BETWEEN CONTEXTS

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : Type} → X ∈ Γ → X ∈ Γ'

variable
  r r' : Ren Γ Γ'

-- IDENTITY, COMPOSITION, AND EXCHANGE RENAMINGS

idr : Ren Γ Γ 
idr x = x

-- WEAKENING OF RENAMINGS

wk₁ : Ren Γ (Γ ∷ X)
wk₁ = Tl

wk₂ : Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
wk₂ f Hd = Hd
wk₂ f (Tl v) = Tl (f v)

-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

V-rename : Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X
M-rename : Ren Γ Γ' → Γ ⊢M⦂ X → Γ' ⊢M⦂ X
T-rename : Ren Γ Γ' → Γ ⊢T⦂ X ⊸ Y → Γ' ⊢T⦂ X ⊸ Y

V-rename f (` x) =
  ` f x
V-rename f (`` c) =
  `` c
V-rename f (ƛ M) =
  ƛ (M-rename (wk₂ f) M)
V-rename f ⟨ V ⟩ =
  ⟨ V-rename f V ⟩

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

variable
  s s' : Sub Γ Γ'

-- IDENTITY AND EXTENSION SUBSTITUTIONS

ids : Sub Γ Γ
ids x = ` x

_[_]s : Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl x) = s x

-- LIFTING SUBSTITUTIONS

lift : Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)

-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

infix 40 _[_]v
infix 40 _[_]m

_[_]v : Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X

_[_]m : Γ ⊢M⦂ X → Sub Γ Γ' → Γ' ⊢M⦂ X

_[_]t : Γ ⊢T⦂ X ⊸ Y → Sub Γ Γ' → Γ' ⊢T⦂ X ⊸ Y

(` x) [ s ]v =
  s x
(`` c) [ s ]v =
  `` c
(ƛ M) [ s ]v =
  ƛ (M [ lift s ]m)
⟨ V ⟩ [ s ]v =
  ⟨ V [ s ]v ⟩

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

strengthen-val : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A → Γ ⊢V⦂ ``` A
strengthen-val (` Tl x) = ` x
strengthen-val (`` c) = `` c

-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- WITH INLINED EVALUATION CONTEXT RULES

infix 10 _↝_

data _↝_ : Γ ⊢M⦂ Y → Γ ⊢M⦂ Y → Set where

  -- COMPUTATIONAL RULES

  apply           : (M : Γ ∷ X ⊢M⦂ Y)
                    (V : Γ ⊢V⦂ X) →
                    ------------
                    ƛ M · V
                    ↝
                    M [ ids [ V ]s ]m

  let-return      : (V : Γ ⊢V⦂ X)
                    (N : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    let= return V `in N
                    ↝
                    N [ ids [ V ]s ]m

  T-↑             : (T : Γ ⊢T⦂ X ⊸ Y)
                    (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ⊢M⦂ X) →
                    ------------
                    T aT (↑ op V M)
                    ↝
                    ↑ op V (T aT M)

  T-promise       : (T : Γ ⊢T⦂ Z ⊸ Y)
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Z) →
                    --------------------------
                    T aT (promise op ↦ M `in N)
                    ↝
                    (promise op ↦ M `in (T-rename wk₁ T aT N))

  T-await         : (T : Γ ⊢T⦂ Y ⊸ Z) 
                    (V : Γ ⊢V⦂ ⟨ X ⟩)
                    (M : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    T aT (await V until M)
                    ↝
                    await V until ((T-rename wk₁ T) aT M)

  promise-↑       : (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op'))
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    --------------------
                    promise op ↦ M `in (↑ op' V N)
                    ↝
                    ↑ op' (strengthen-val V) (promise op ↦ M `in N)

  ↓-return        : (V : Γ ⊢V⦂ ```(payload op))
                    (W : Γ ⊢V⦂ Y) →
                    ------------
                    ↓ op V (return W)
                    ↝
                    return W

  ↓-promise-op    : (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    --------------------
                    ↓ op V (promise op ↦ M `in N)
                    ↝
                    let= coerce (M [ ids [ V ]s ]m) `in (↓ op (V-rename wk₁ V) N)

  await-promise   : (V : Γ ⊢V⦂ X)
                    (M : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    await ⟨ V ⟩ until M
                    ↝
                    M [ ids [ V ]s ]m

  ↑-discard       : (V : Γ ⊢V⦂ ```(payload op)) →
                    --------
                    ↑ op V M
                    ↝
                    M

  -- INLINED EVALUATION CONTEXT RULES

  context-↑       : N ↝ N' →
                    -----
                    ↑ op V N
                    ↝
                    ↑ op V N'

  context-promise : N ↝ N' →
                    -----
                    promise op ↦ M `in N
                    ↝
                    promise op ↦ M `in N'

  context-T       : (T : Γ ⊢T⦂ X ⊸ Y) →
                    M ↝ M' →
                    -----
                    T aT M
                    ↝
                    T aT M'

  coerce-return   : (V : Γ ⊢V⦂ Y) →
                    ------------
                    coerce (return V)
                    ↝
                    return V