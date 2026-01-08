open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.List using (List) renaming ([] to []ₗ; _∷_ to _∷ₗ_; [_] to [_]ₗ)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import AEffFinSN.FiniteEffectAnnotations

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload; Σ-base; ar-base)
open import AEff.Types using (GType)

module AEffFinSN.AEff where

data VType : Set

data CType : Set

infix 30 _⇒_
data VType where
  ``` : GType → VType
  _⇒_ : VType → CType → VType
  ⟨_⟩ : VType → VType

infix 30 _!_
data CType where
  _!_ : VType → Σ[ i ∈ I ] isfin i → CType

variable
  X Y Z : VType
  C D E : CType

v-of : CType → VType
v-of (X ! _) = X

i-of : CType → I
i-of (_ ! (i , _)) = i

isf-of : (C : CType) → isfin (i-of C)
isf-of (_ ! (_ , isf)) = isf

infixl 30 _∷_
data Ctx : Set where
  []  : Ctx
  _∷_ : Ctx → VType → Ctx

variable
  Γ Γ' Δ Δ' : Ctx

data _∈_ (X : VType) : Ctx → Set where
  Hd : X ∈ Γ ∷ X
  Tl : X ∈ Γ → X ∈ Γ ∷ Y

data _⊢V⦂_ : Ctx → VType → Set

data _⊢M⦂_ : Ctx → CType → Set

data _⊢V⦂_ where
  `_  : X ∈ Γ → Γ ⊢V⦂ X
  ``_ : (c : Σ-base) → Γ ⊢V⦂ ```(ar-base c)
  ƛ   : Γ ∷ X ⊢M⦂ C → Γ ⊢V⦂ X ⇒ C
  ⟨_⟩ : Γ ⊢V⦂ X → Γ ⊢V⦂ ⟨ X ⟩

data _⊢M⦂_ where

  return             : Γ ⊢V⦂ X →
                       -------
                       Γ ⊢M⦂ X ! (i , isf)

  _·_                : Γ ⊢V⦂ X ⇒ C →
                       Γ ⊢V⦂ X →
                       -------
                       Γ ⊢M⦂ C

  let=_`in_          : Γ ⊢M⦂ X ! (i , isf) →
                       Γ ∷ X ⊢M⦂ Y ! (i , isf) →
                       -------
                       Γ ⊢M⦂ Y ! (i , isf)

  ↑                  : (op : Σₛ) →
                       Γ ⊢V⦂ ```(payload op) →
                       Γ ⊢M⦂ C →
                       --------------
                       Γ ⊢M⦂ C

  ↓                  : (op : Σₛ) →
                       Γ ⊢V⦂ ```(payload op) →
                       Γ ⊢M⦂ C →
                       --------------
                       Γ ⊢M⦂ v-of C ! (op ↓ₑ i-of C , fin-↓ₑ op (isf-of C))

  promise_∣_,_↦_`in_ : (op : Σₛ) →
                       i' ⊑ lkp op (i-of C) →
                       [ op ]ₗ ∈ᵢ i-of C →
                       Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (i' , isf') →
                       Γ ∷ ⟨ X ⟩ ⊢M⦂ C →
                       ------------------
                       Γ ⊢M⦂ C

  await_until_       : Γ ⊢V⦂ ⟨ X ⟩ →
                       Γ ∷ X ⊢M⦂ C →
                       -------
                       Γ ⊢M⦂ C

  coerce             : i ⊑ i' →
                       Γ ⊢M⦂ X ! (i , isf) →
                       -------------------
                       Γ ⊢M⦂ X ! (i' , isf')

variable
  V V' W W' U U' : Γ ⊢V⦂ X
  M M' N N' L L' : Γ ⊢M⦂ C

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : VType} → X ∈ Γ → X ∈ Γ'

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
M-rename r (promise op ∣ p , q ↦ M `in N) =
  promise op ∣ p , q ↦ M-rename (wk₂ r) M `in M-rename (wk₂ r) N
M-rename r (await V until N) =
  await V-rename r V until M-rename (wk₂ r) N
M-rename r (coerce p M) =
  coerce p (M-rename r M)

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈ Γ → Γ' ⊢V⦂ X

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
(promise op ∣ p , q ↦ M `in N) [ s ]m =
  promise op ∣ p , q ↦ M [ lift s ]m `in N [ lift s ]m
(await V until N) [ s ]m =
  await V [ s ]v until N [ lift s ]m
(coerce p M) [ s ]m =
  coerce p (M [ s ]m)

strengthen-val : {A : GType} → Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A → Γ ⊢V⦂ ``` A
strengthen-val (` Tl x) = ` x
strengthen-val (`` c) = `` c

infix 10 _↝↝_
data _↝↝_ : Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

    apply           : (M : Γ ∷ X ⊢M⦂ C)
                      (V : Γ ⊢V⦂ X) →
                      ----------------------
                      ƛ M · V
                      ↝↝
                      M [ id-subst [ V ]s ]m

    let-return      : (V : Γ ⊢V⦂ X)
                      (N : Γ ∷ X ⊢M⦂ Y ! (i , isf)) →
                      -----------------------------
                      let= return V `in N
                      ↝↝
                      N [ id-subst [ V ]s ]m

    let-↑           : (V : Γ ⊢V⦂ ```(payload op))
                      (M : Γ ⊢M⦂ X ! (i , isf))
                      (N : Γ ∷ X ⊢M⦂ Y ! (i , isf)) →
                      -----------------------------
                      let= ↑ op V M `in N
                      ↝↝
                      ↑ op V (let= M `in N)

    let-promise     : (p : i' ⊑ lkp op i)
                      (q : [ op ]ₗ ∈ᵢ i)
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (i' , isf'))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf))
                      (L : Γ ∷ Y ⊢M⦂ Z ! (i , isf)) →
                      ----------------------------------
                      let= promise op ∣ p , q ↦ M `in N `in L
                      ↝↝
                      promise op ∣ p , q ↦ M `in let= N `in (M-rename (wk₂ wk₁) L)

    let-await       : (V : Γ ⊢V⦂ ⟨ X ⟩)
                      (M : Γ ∷ X ⊢M⦂ Y ! (i , isf))
                      (N : Γ ∷ Y ⊢M⦂ Z ! (i , isf)) →
                      --------------------------
                      let= await V until M `in N
                      ↝↝
                      await V until let= M `in M-rename (wk₂ wk₁) N

    ↓-await         : (W : Γ ⊢V⦂ ```(payload op))
                      (V : Γ ⊢V⦂ ⟨ X ⟩)
                      (M : Γ ∷ X ⊢M⦂ C) →
                      ------------------------
                      ↓ op W (await V until M)
                      ↝↝
                      await V until ↓ op (V-rename (wk₁ {X = X}) W) M

    promise-↑       : (p : i' ⊑ lkp op i)
                      (q : [ op ]ₗ ∈ᵢ i)
                      (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op'))
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (i' , isf'))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf)) →
                      --------------------------------------------
                      promise op ∣ p , q ↦ M `in (↑ op' V N)
                      ↝↝
                      ↑ op' (strengthen-val V) (promise op ∣ p , q ↦ M `in N)

    ↓-return        : (V : Γ ⊢V⦂ ```(payload op))
                      (W : Γ ⊢V⦂ X) →
                      ------------------------
                      ↓ op V (return {i = i} {isf} W)
                      ↝↝
                      return W

    ↓-↑             : (V : Γ ⊢V⦂ ```(payload op))
                      (W : Γ ⊢V⦂ ```(payload op'))
                      (M : Γ ⊢M⦂ X ! (i , isf)) →
                      -------------------------------
                      ↓ op V (↑ op' W M)
                      ↝↝
                      ↑ op' W (↓ op V M)

    ↓-promise-op    : (p : i' ⊑ lkp op i)
                      (q : [ op ]ₗ ∈ᵢ i)
                      (V : Γ ⊢V⦂ ```(payload op))
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (i' , isf'))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf)) →
                      --------------------------------
                      ↓ op V (promise op ∣ p , q ↦ M `in N)
                      ↝↝
                      let= coerce (⊑-trans p ∪-inr) (M [ id-subst [ V ]s ]m) `in ↓ op (V-rename wk₁ V) N

    ↓-promise-op'   : (V : Γ ⊢V⦂ ```(payload op))
                      (p : i' ⊑ lkp op' i)
                      (q : [ op' ]ₗ ∈ᵢ i)
                      (r : op ≢ op')
                      (M : Γ ∷ ```(payload op') ⊢M⦂ ⟨ X ⟩ ! (i' , isf'))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf)) →
                      ------------------------------------------------------------------------
                      ↓ op V (promise op' ∣ p , q ↦ M `in N)
                      ↝↝
                      promise op' ∣ ⊑-trans p (lkp-↓ₑ-≢ i r) , ∈-∪-i₁ (∈-[↦]-i r q) ↦ M `in ↓ op (V-rename wk₁ V) N

    await-promise   : (V : Γ ⊢V⦂ X)
                      (N : Γ ∷ X ⊢M⦂ C) →
                      --------------------
                      await ⟨ V ⟩ until N
                      ↝↝
                      N [ id-subst [ V ]s ]m

    -- INLINED EVALUATION CONTEXT RULES

    context-let     : M ↝↝ M' → 
                      -------------
                      let= M `in N
                      ↝↝
                      let= M' `in N

    context-↑       : M ↝↝ N →
                      ----------
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
                      promise op ∣ x , y ↦ M `in N
                      ↝↝
                      promise op ∣ x , y ↦ M `in N'

    context-coerce  : M ↝↝ M' →
                      -----------
                      coerce {isf' = isf'} x M
                      ↝↝
                      coerce x M'

    -- COERCION RULES

    coerce-return   : (V : Γ ⊢V⦂ X) →
                      --------------------------------
                      coerce {isf = isf} {isf' = isf'} x (return V)
                      ↝↝
                      return V

    coerce-↑        : (V : Γ ⊢V⦂ ```(payload op))
                      (M : Γ ⊢M⦂ X ! (i , isf)) →
                      -------------------------------
                      coerce {isf' = isf'} x (↑ op V M)
                      ↝↝
                      ↑ op V (coerce x M)

    coerce-promise  : (x : i ⊑ i'')
                      (p : i' ⊑ lkp op i)
                      (q : [ op ]ₗ ∈ᵢ i)
                      (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (i' , isf'))
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (i , isf)) →
                      ------------------------------------------------------------------
                      coerce {isf' = isf''} x (promise op ∣ p , q ↦ M `in N)
                      ↝↝
                      promise op ∣ ⊑-trans p (lkp-mono x) , ∈ᵢ-⊑ x q ↦ M `in coerce x N

type-of : Γ ⊢M⦂ C → CType
type-of {C = C} _ = C


-- FLATTENED PARALLEL PROCESSES

infix 10 _⊢P⦂
data _⊢P⦂ Γ : Set where
  []  : Γ ⊢P⦂
  _∥_ : Γ ⊢M⦂ C → Γ ⊢P⦂ → Γ ⊢P⦂

variable
  P P' Q Q' : Γ ⊢P⦂

↓ₜ : (op : Σₛ) → Γ ⊢V⦂ ```(payload op) → Γ ⊢P⦂ → Γ ⊢P⦂
↓ₜ op V [] = []
↓ₜ op V (M ∥ P) = ↓ op V M ∥ ↓ₜ op V P


-- THE REDUCTION THAT SENDS A SIGNAL FROM A COMPUTATION TO ALL THE OTHER COMPUTATIONS IN ONE STEP

infix 10 _↝↝ₚ-[_,_]_
data _↝↝ₚ-[_,_]_ : Γ ⊢P⦂ → (op : Σₛ) → Γ ⊢V⦂ ```(payload op) → Γ ⊢P⦂ → Set where

  ↑-∥ₗ : --------------
         ↑ op V M ∥ P
         ↝↝ₚ-[ op , V ]
         M ∥ ↓ₜ op V P

  ↑-∥ᵣ : P ↝↝ₚ-[ op , V ] Q →
         -------------
         M ∥ P
         ↝↝ₚ-[ op , V ]
         ↓ op V M ∥ Q


-- THE REDUCTION THAT RUNS ONE OF THE COMPUTATION IN A PARALLEL PROCESS

infix 10 _↝↝ₚ-↝_
data _↝↝ₚ-↝_ : Γ ⊢P⦂ → Γ ⊢P⦂ → Set where

  context-∥ₗ : M ↝↝ N →
               -----
               M ∥ P
               ↝↝ₚ-↝
               N ∥ P

  context-∥ᵣ : P ↝↝ₚ-↝ Q →
               -----
               M ∥ P
               ↝↝ₚ-↝
               M ∥ Q


-- A REDUCTION OF A PARALLEL PROCESS IS EITHER A REDUCTION IN ONE OF THE COMPUTATION
-- OR THE SENDING OF A SIGNALS FROM ONE COMPUTATION TO ALL THE OTHERS

infix 10 _↝↝ₚ_
data _↝↝ₚ_ : Γ ⊢P⦂ → Γ ⊢P⦂ → Set where
  ↑-∥ : P ↝↝ₚ-[ op , V ] Q → P ↝↝ₚ Q
  run : P ↝↝ₚ-↝ Q → P ↝↝ₚ Q