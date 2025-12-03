{-# OPTIONS --guardedness #-}

open import Data.Product

open import Relation.Binary.PropositionalEquality

open import AEffFinSN.FiniteEffectAnnotations

open import EffectAnnotations using (Σₛ)
open import AEff using (payload; Σ-base; ar-base)
open import Types using (GType)

open import AEffStarSN.AEffStar using () renaming (Type to Type*; Ctx to Ctx*; ``` to ```*; _⇒_ to _⇒*_; ⟨_⟩ to ⟨_⟩*; [] to []*; _∷_ to _∷*_)

module AEffFinSN.AEffFin where

variable
  A B   : GType
  Xs Ys Zs : Type*
  Γs Δs : Ctx*

data VType : Type* → Set

data CType : Type* → Set

infix 30 _⇒_
data VType where
  ``` : (A : GType) → VType (```* A)
  _⇒_ : VType Xs → CType Ys → VType (Xs ⇒* Ys)
  ⟨_⟩ : VType Xs → VType (⟨ Xs ⟩*)

infix 30 _!_
data CType where
  _!_ : VType Xs → Σ[ i ∈ I ] isfin i → CType Xs

variable
  X Y Z : VType Xs
  C D E : CType Xs

infixl 30 _∷_
data Ctx : Ctx* → Set where
  []  : Ctx []*
  _∷_ : Ctx Γs → VType Xs → Ctx (Γs ∷* Xs)

variable
  Γ Γ' Δ Δ' Ε Ε' : Ctx Γs

data _∈_ (X : VType Xs) : Ctx Γs → Set where
  Hd : X ∈ Γ ∷ X
  Tl : X ∈ Γ → X ∈ Γ ∷ Y

data _⊢V⦂_ : Ctx Γs → VType Xs → Set

data _⊢M⦂_ : Ctx Γs → CType Xs → Set

data _⊢V⦂_ where
  `_  : X ∈ Γ → Γ ⊢V⦂ X
  ``_ : (c : Σ-base) → Γ ⊢V⦂ ```(ar-base c)
  ƛ   : Γ ∷ X ⊢M⦂ C → Γ ⊢V⦂ X ⇒ C
  ⟨_⟩ : Γ ⊢V⦂ X → Γ ⊢V⦂ ⟨ X ⟩

data _⊢M⦂_ where

  return           : Γ ⊢V⦂ X →
                     -------
                     Γ ⊢M⦂ X ! (i , isf)

  _·_              : Γ ⊢V⦂ X ⇒ C →
                     Γ ⊢V⦂ X →
                     -------
                     Γ ⊢M⦂ C

  let=_`in_        : Γ ⊢M⦂ X ! (i , isf) →
                     Γ ∷ X ⊢M⦂ Y ! (i , isf) →
                     -------
                     Γ ⊢M⦂ Y ! (i , isf)

  ↑                : (op : Σₛ) →
                     Γ ⊢V⦂ ```(payload op) →
                     Γ ⊢M⦂ X ! (i , isf) →
                     --------------
                     Γ ⊢M⦂ X ! (i , isf)

  ↓                : (op : Σₛ) →
                     Γ ⊢V⦂ ```(payload op) →
                     Γ ⊢M⦂ X ! (i , isf) →
                     --------------
                     Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf)

  promise_∣_↦_`in_ : (op : Σₛ) →
                     isnode (lkp op i) →
                     Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (lkp op i , fin-lkp op isf) →
                     Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf) →
                     ------------------
                     Γ ⊢M⦂ Y ! (i , isf)

  await_until_     : Γ ⊢V⦂ ⟨ X ⟩ →
                     Γ ∷ X ⊢M⦂ Y ! (i , isf) →
                     ------------------
                     Γ ⊢M⦂ Y ! (i , isf)

  coerce           : i ⊑i i' →
                     Γ ⊢M⦂ X ! (i , isf) →
                     -------------------
                     Γ ⊢M⦂ X ! (i' , isf')

variable
  V V' W W' U U' : Γ ⊢V⦂ X
  M M' N N' L L' : Γ ⊢M⦂ C

Ren : Ctx Γs → Ctx Δs → Set
Ren Γ Γ' = {Xs : Type*} {X : VType Xs} → X ∈ Γ → X ∈ Γ'

id-ren : Ren Γ Γ 
id-ren x = x

wk₁ : Ren Γ (Γ ∷ X)
wk₁ = Tl

wk₂ : Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
wk₂ f Hd = Hd
wk₂ f (Tl v) = Tl (f v)

V-rename : Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X

M-rename : Ren Γ Γ' → Γ ⊢M⦂ C → Γ' ⊢M⦂ C

V-rename r (` x) = ` r x
V-rename r (`` c) = `` c
V-rename r (ƛ M) = ƛ (M-rename (wk₂ r) M)
V-rename r (⟨ V ⟩) = ⟨ V-rename r V ⟩

M-rename r (return V) =
  return (V-rename r V)
M-rename r (let= M `in N) =
  let= M-rename r M `in M-rename (wk₂ r) N
M-rename r (V · W) =
  V-rename r V · V-rename r W
M-rename r (↑ op V M) =
  ↑ op (V-rename r V) (M-rename r M)
M-rename r (↓ op V M) =
  ↓ op (V-rename r V) (M-rename r M)
M-rename r (promise op ∣ p ↦ M `in N) =
  promise op ∣ p ↦ M-rename (wk₂ r) M `in M-rename (wk₂ r) N
M-rename r (await V until N) =
  await V-rename r V until M-rename (wk₂ r) N
M-rename r (coerce p M) =
  coerce p (M-rename r M)

Sub : Ctx Γs → Ctx Δs → Set
Sub Γ Γ' = {Xs : Type*} {X : VType Xs} → X ∈ Γ → Γ' ⊢V⦂ X

id-subst : Sub Γ Γ
id-subst x = ` x

_[_]s : Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl x) = s x

lift : Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)

infix 40 _[_]v
infix 40 _[_]m

_[_]v : Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X

_[_]m : Γ ⊢M⦂ C → Sub Γ Γ' → Γ' ⊢M⦂ C

(` x) [ s ]v =
  s x
(`` c) [ s ]v =
  `` c
(ƛ M) [ s ]v =
  ƛ (M [ lift s ]m)
(⟨ V ⟩) [ s ]v =
  ⟨ V [ s ]v ⟩

(return V) [ s ]m =
  return (V [ s ]v)
(let= M `in N) [ s ]m =
  let= M [ s ]m `in N [ lift s ]m
(V · W) [ s ]m =
  V [ s ]v · W [ s ]v
(↑ op V M) [ s ]m =
  ↑ op (V [ s ]v) (M [ s ]m)
(↓ op V M) [ s ]m =
  ↓ op (V [ s ]v) (M [ s ]m)
(promise op ∣ p ↦ M `in N) [ s ]m =
  promise op ∣ p ↦ M [ lift s ]m `in N [ lift s ]m
(await V until N) [ s ]m =
  await V [ s ]v until N [ lift s ]m
(coerce p M) [ s ]m =
  coerce p (M [ s ]m)

strengthen-val : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A → Γ ⊢V⦂ ``` A
strengthen-val (` Tl x) = ` x
strengthen-val (`` c) = `` c

infix 10 _↝_
data _↝_ : Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

    apply           : (M : Γ ∷ X ⊢M⦂ C)
                      (V : Γ ⊢V⦂ X) →
                      ----------------------
                      ƛ M · V
                      ↝
                      M [ id-subst [ V ]s ]m

    let-return      : (V : Γ ⊢V⦂ X)
                      (N : Γ ∷ X ⊢M⦂ Y ! (i , isf)) →
                      -----------------------------
                      let= return V `in N
                      ↝
                      N [ id-subst [ V ]s ]m

    let-↑           : (V : Γ ⊢V⦂ ```(payload op))
                      (M : Γ ⊢M⦂ X ! (i , isf))
                      (N : Γ ∷ X ⊢M⦂ Y ! (i , isf)) →
                      -----------------------------
                      let= ↑ op V M `in N
                      ↝
                      ↑ op V (let= M `in N)

    let-promise     : (p : isnode (lkp op i))
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (lkp op i , fin-lkp op isf))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf))
                      (L : Γ ∷ Y ⊢M⦂ Z ! (i , isf)) →
                      ----------------------------------
                      let= promise op ∣ p ↦ M `in N `in L
                      ↝
                      promise op ∣ p ↦ M `in let= N `in (M-rename (wk₂ wk₁) L)

    promise-↑       : (p : isnode (lkp op i))
                      (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op'))
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (lkp op i , fin-lkp op isf))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf)) →
                      --------------------------------------------
                      promise op ∣ p ↦ M `in (↑ op' V N)
                      ↝
                      ↑ op' (strengthen-val V) (promise op ∣ p ↦ M `in N)

    ↓-return        : (V : Γ ⊢V⦂ ```(payload op))
                      (W : Γ ⊢V⦂ X) →
                      ------------------------
                      ↓ {i = i} {isf} op V (return W)
                      ↝
                      return W

    ↓-↑             : (V : Γ ⊢V⦂ ```(payload op))
                      (W : Γ ⊢V⦂ ```(payload op'))
                      (M : Γ ⊢M⦂ X ! (i , isf)) →
                      -------------------------------
                      ↓ op V (↑ op' W M)
                      ↝
                      ↑ op' W (↓ op V M)

    ↓-promise-op    : (p : isnode (lkp op i))
                      (V : Γ ⊢V⦂ ```(payload op))
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (lkp op i , fin-lkp op isf))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf)) →
                      --------------------------------
                      ↓ op V (promise op ∣ p ↦ M `in N)
                      ↝
                      let= coerce (↓ₑ-⊑i {i = i}) (M [ id-subst [ V ]s ]m) `in ↓ op (V-rename wk₁ V) N

    ↓-promise-op'   : (V : Γ ⊢V⦂ ```(payload op))
                      (q : isnode (lkp op' i))
                      (p : op ≢ op')
                      (M : Γ ∷ ```(payload op') ⊢M⦂ ⟨ X ⟩ ! (lkp op' i , fin-lkp op' isf))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf)) →
                      ------------------------------------------------------------------------
                      ↓ op V (promise op' ∣ q ↦ M `in N)
                      ↝
                      promise op' ∣ isnode-⊑i (lkp-↓ₑ-≢ {i = i} p) q ↦ coerce (lkp-↓ₑ-≢ {i = i} p) M `in ↓ op (V-rename wk₁ V) N

    await-promise   : (V : Γ ⊢V⦂ X) →
                      (N : Γ ∷ X ⊢M⦂ Y ! (i , isf)) →
                      --------------------
                      await ⟨ V ⟩ until N
                      ↝
                      N [ id-subst [ V ]s ]m

    -- INLINED EVALUATION CONTEXT RULES

    context-let     : M ↝ M' → 
                      -------------
                      let= M `in N
                      ↝
                      let= M' `in N

    context-↑       : M ↝ N →
                      ----------
                      ↑ op V M
                      ↝
                      ↑ op V N

    context-↓       : M ↝ N →
                      ---------
                      ↓ op V M
                      ↝
                      ↓ op V N

    context-promise : {p : isnode (lkp op i)}
                      {M M' : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (lkp op i , fin-lkp op isf)}
                      {N N' : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf)} →
                      N ↝ N' →
                      ---------------------
                      promise op ∣ p ↦ M `in N
                      ↝
                      promise op ∣ p ↦ M `in N'

    -- COERCION RULES

    coerce-return   : {q : i ⊑i i'}
                      (V : Γ ⊢V⦂ X) →
                      --------------------------------
                      coerce {isf = isf} {isf' = isf'} q (return V)
                      ↝
                      return V

    coerce-↑        : {q : i ⊑i i'}
                      (V : Γ ⊢V⦂ ```(payload op))
                      (M : Γ ⊢M⦂ X ! (i , isf)) →
                      -------------------------------
                      coerce {isf' = isf'} q (↑ op V M)
                      ↝
                      ↑ op V (coerce q M)

    coerce-promise  : {q : i ⊑i i'}
                      (p : isnode (lkp op i))
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (lkp op i , fin-lkp op isf))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf)) →
                      ------------------------------------------------------------------
                      coerce {isf' = isf'} q (promise op ∣ p ↦ M `in N)
                      ↝
                      promise op ∣ isnode-⊑i (lkp-mono q) p ↦ coerce (lkp-mono q) M `in coerce q N