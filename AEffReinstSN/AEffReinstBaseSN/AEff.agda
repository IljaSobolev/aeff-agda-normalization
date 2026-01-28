{-# OPTIONS --guardedness #-}

open import Data.List using (List; []) renaming (_∷_ to _∷ₗ_)

open import AEffReinstSN.CoinductiveEffectAnnotations using (Σₛ)
open import AEffReinstSN.AEff using (payload; Σ-base; ar-base)
open import AEffReinstSN.Types using (BType; GType)

open import Relation.Binary.PropositionalEquality using (_≢_)

module AEffReinstSN.AEffReinstBaseSN.AEff where

variable
  A : BType
  op op' : Σₛ

-- VALUE AND COMPUTATION TYPES

infix 30 _⇒_
infix 35 _+_

data Type : Set where
  ``` : GType → Type
  𝟙   : Type
  _⇒_ : Type → Type → Type
  _+_ : Type → Type → Type
  ⟨_⟩ : Type → Type

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

-- DERIVATIONS OF WELL-TYPED TERMS

data _⊢V⦂_ (Γ : Ctx) : Type → Set

data _⊢M⦂_ (Γ : Ctx) (Y : Type) : Set

data _⊢V⦂_ Γ where
  `_  : X ∈ Γ → Γ ⊢V⦂ X
  ``_ : (c : Σ-base) → Γ ⊢V⦂ ```(ar-base c)
  ƛ   : Γ ∷ X ⊢M⦂ Y → Γ ⊢V⦂ X ⇒ Y
  ⟨_⟩ : Γ ⊢V⦂ X → Γ ⊢V⦂ ⟨ X ⟩
  inl : Γ ⊢V⦂ X → Γ ⊢V⦂ X + Y
  inr : Γ ⊢V⦂ Y → Γ ⊢V⦂ X + Y
  ★   : Γ ⊢V⦂ 𝟙

infix 40 _·_
data _⊢M⦂_ Γ Y where

  return         : Γ ⊢V⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  _·_            : Γ ⊢V⦂ X ⇒ Y →
                   Γ ⊢V⦂ X →
                   -------
                   Γ ⊢M⦂ Y

  let=_`in_      : Γ ⊢M⦂ X →
                   Γ ∷ X ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  ↑              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  ↓              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  promise_↦_`in_ : (op : Σₛ) →
                   Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙 →
                   Γ ∷ ⟨ X ⟩ ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  await_until_   : Γ ⊢V⦂ ⟨ X ⟩ →
                   Γ ∷ X ⊢M⦂ Y →
                   -------
                   Γ ⊢M⦂ Y

  match+         : Γ ⊢V⦂ X + Z →
                   Γ ∷ X ⊢M⦂ Y →
                   Γ ∷ Z ⊢M⦂ Y →
                   --------
                   Γ ⊢M⦂ Y

variable
  V V' W W' : Γ ⊢V⦂ X
  M M' N N' L L' : Γ ⊢M⦂ X

-- SET OF RENAMINGS BETWEEN CONTEXTS

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : Type} → X ∈ Γ → X ∈ Γ'

variable
  r r' : Ren Γ Γ'

-- IDENTITY, COMPOSITION, AND EXCHANGE RENAMINGS

id-ren : Ren Γ Γ 
id-ren {X} x = x

-- WEAKENING OF RENAMINGS

wk₁ : Ren Γ (Γ ∷ X)
wk₁ = Tl

wk₂ : Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
wk₂ f Hd = Hd
wk₂ f (Tl v) = Tl (f v)

-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

V-rename : Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X

M-rename : Ren Γ Γ' → Γ ⊢M⦂ X → Γ' ⊢M⦂ X

V-rename f (` x) =
  ` f x
V-rename f (`` c) =
  `` c
V-rename f (ƛ M) =
  ƛ (M-rename (wk₂ f) M)
V-rename f ⟨ V ⟩ =
  ⟨ V-rename f V ⟩
V-rename f (inl V) =
  inl (V-rename f V)
V-rename f (inr V) =
  inr (V-rename f V)
V-rename f ★ =
  ★

M-rename f (return V) =
  return (V-rename f V)
M-rename f (V · W) =
  V-rename f V · V-rename f W
M-rename f (let= M `in N) =
  let= M-rename f M `in M-rename (wk₂ f) N
M-rename f (↑ op V M) =
  ↑ op (V-rename f V) (M-rename f M)
M-rename f (↓ op V M) =
  ↓ op (V-rename f V) (M-rename f M)
M-rename f (promise op ↦ M `in N) =
  promise op ↦ M-rename (wk₂ f) M `in M-rename (wk₂ f) N
M-rename f (await V until M) =
  await (V-rename f V) until (M-rename (wk₂ f) M)
M-rename f (match+ V M N) =
  match+ (V-rename f V) (M-rename (wk₂ f) M) (M-rename (wk₂ f) N)

-- SET OF SUBSTITUTIONS BETWEEN CONTEXTS

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : Type} → X ∈ Γ → Γ' ⊢V⦂ X

variable
  s s' : Sub Γ Γ'

-- IDENTITY AND EXTENSION SUBSTITUTIONS

id-subst : Sub Γ Γ
id-subst x = ` x

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

(` x) [ s ]v =
  s x
(`` c) [ s ]v =
  `` c
(ƛ M) [ s ]v =
  ƛ (M [ lift s ]m)
⟨ V ⟩ [ s ]v =
  ⟨ V [ s ]v ⟩
inl V [ s ]v =
  inl (V [ s ]v)
inr V [ s ]v =
  inr (V [ s ]v)
★ [ s ]v =
  ★

(return V) [ s ]m =
  return (V [ s ]v)
(V · W) [ s ]m =
  (V [ s ]v) · (W [ s ]v)
(let= M `in N) [ s ]m =
  let= M [ s ]m `in N [ lift s ]m
(↑ op V M) [ s ]m =
  ↑ op (V [ s ]v) (M [ s ]m)
(↓ op V M) [ s ]m =
  ↓ op (V [ s ]v) (M [ s ]m)
(promise op ↦ M `in N) [ s ]m =
  promise op ↦ M [ lift s ]m `in (N [ lift s ]m)
(await V until M) [ s ]m =
  await (V [ s ]v) until (M [ lift s ]m)
(match+ V M N) [ s ]m =
  match+ (V [ s ]v) (M [ lift s ]m) (N [ lift s ]m)

-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-val : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A → Γ ⊢V⦂ ``` A
strengthen-val (` Tl x) = ` x
strengthen-val (`` c) = `` c

-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- WITH INLINED EVALUATION CONTEXT RULES

infix 10 _↝↝_
data _↝↝_ : Γ ⊢M⦂ Y → Γ ⊢M⦂ Y → Set where

  -- COMPUTATIONAL RULES

  apply           : (M : Γ ∷ X ⊢M⦂ Y)
                    (V : Γ ⊢V⦂ X) →
                    ------------
                    ƛ M · V
                    ↝↝
                    M [ id-subst [ V ]s ]m

  let-return      : (V : Γ ⊢V⦂ X)
                    (N : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    let= return V `in N
                    ↝↝
                    N [ id-subst [ V ]s ]m

  let-↑           : (N : Γ ∷ X ⊢M⦂ Y)
                    (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ⊢M⦂ X) →
                    ------------
                    let= ↑ op V M `in N
                    ↝↝
                    ↑ op V (let= M `in N)

  ↓-↑             : (V' : Γ ⊢V⦂ ```(payload op'))
                    (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ⊢M⦂ X) →
                    -------------------
                    ↓ op' V' (↑ op V M)
                    ↝↝
                    ↑ op V (↓ op' V' M)

  let-promise     : (L : Γ ∷ Z ⊢M⦂ Y)
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Z) →
                    --------------------------
                    let= promise op ↦ M `in N `in L
                    ↝↝
                    promise op ↦ M `in (let= N `in M-rename (wk₂ wk₁) L)

  let-await       : (N : Γ ∷ Y ⊢M⦂ Z) 
                    (V : Γ ⊢V⦂ ⟨ X ⟩)
                    (M : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    let= await V until M `in N
                    ↝↝
                    await V until let= M `in M-rename (wk₂ wk₁) N

  ↓-await         : (W : Γ ⊢V⦂ ```(payload op))
                    (V : Γ ⊢V⦂ ⟨ X ⟩)
                    (M : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    ↓ op W (await V until M)
                    ↝↝
                    await V until ↓ op (V-rename wk₁ W) M

  promise-↑       : (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op'))
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    --------------------
                    promise op ↦ M `in (↑ op' V N)
                    ↝↝
                    ↑ op' (strengthen-val V) (promise op ↦ M `in N)

  ↓-return        : (V : Γ ⊢V⦂ ```(payload op))
                    (W : Γ ⊢V⦂ Y) →
                    ------------
                    ↓ op V (return W)
                    ↝↝
                    return W

  ↓-promise-op    : (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    -----------------------------
                    ↓ op V (promise op ↦ M `in N)
                    ↝↝
                    let=
                      (let=
                        M [ id-subst [ V ]s ]m `in
                        (match+ (` Hd)
                          (return (` Hd))
                          (M-rename wk₁ (M-rename wk₁ (promise op ↦ M `in return (` Hd)))))) `in
                      ↓ op (V-rename wk₁ V) N

  ↓-promise-op'   : (p : op ≢ op')
                    (V : Γ ⊢V⦂ ```(payload op'))
                    (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ + 𝟙)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    -------------------------------
                    ↓ op' V (promise op ↦ M `in N)
                    ↝↝
                    promise op ↦ M `in ↓ op' (V-rename wk₁ V) N

  match+-inl      : (V : Γ ⊢V⦂ X)
                    (M : Γ ∷ X ⊢M⦂ Y)
                    (N : Γ ∷ Z ⊢M⦂ Y) →
                    -----------------
                    match+ (inl V) M N
                    ↝↝
                    M [ id-subst [ V ]s ]m

  match+-inr      : (V : Γ ⊢V⦂ Z)
                    (M : Γ ∷ X ⊢M⦂ Y)
                    (N : Γ ∷ Z ⊢M⦂ Y) →
                    -----------------
                    match+ (inr V) M N
                    ↝↝
                    N [ id-subst [ V ]s ]m

  await-promise   : (V : Γ ⊢V⦂ X)
                    (M : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    await ⟨ V ⟩ until M
                    ↝↝
                    M [ id-subst [ V ]s ]m

  -- INLINED EVALUATION CONTEXT RULES

  context-↑       : N ↝↝ N' →
                    -----
                    ↑ op V N
                    ↝↝
                    ↑ op V N'

  context-promise : N ↝↝ N' →
                    -----
                    promise op ↦ M `in N
                    ↝↝
                    promise op ↦ M `in N'

  context-let     : M ↝↝ M' →
                    -----
                    let= M `in N
                    ↝↝
                    let= M' `in N

  context-↓       : M ↝↝ M' →
                    -----
                    ↓ op V M
                    ↝↝
                    ↓ op V M'