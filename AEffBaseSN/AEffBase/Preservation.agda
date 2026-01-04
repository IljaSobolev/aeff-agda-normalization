open import AEffBaseSN.AEffBase.Types
open import AEffBaseSN.AEffBase.AEff
open import AEffBaseSN.AEffBase.Renamings
open import AEffBaseSN.AEffBase.Substitutions

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

open import Data.List using (List) renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Relation.Binary.PropositionalEquality using (_≢_)

module AEffBaseSN.AEffBase.Preservation where

-- BINDING CONTEXTS

BCtx = List Type

variable
  Δb : BCtx

-- WELL-TYPED EVALUATION CONTEXTS

data _⊢E[_]⦂_ (Γ : Ctx) : BCtx → Type → Set where

  [-]            : --------------
                   Γ ⊢E[ []ₗ ]⦂ X

  let=_`in_      : Γ ⊢E[ Δb ]⦂ X →
                   Γ ∷ X ⊢M⦂ Y →
                   -------------
                   Γ ⊢E[ Δb ]⦂ Y

  ↑              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ⊢E[ Δb ]⦂ X →
                   -------------
                   Γ ⊢E[ Δb ]⦂ X

  ↓              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ⊢E[ Δb ]⦂ X →
                   -------------
                   Γ ⊢E[ Δb ]⦂ X

  promise_↦_`in_ : (op : Σₛ) →
                   Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ →
                   Γ ∷ ⟨ X ⟩ ⊢E[ Δb ]⦂ Y →
                   ------------------
                   Γ ⊢E[ X ∷ₗ Δb ]⦂ Y


-- MERGING AN ORDINARY CONTEXT AND A BINDING CONTEXT

infix 30 _⋈_
_⋈_ : Ctx → BCtx → Ctx
Γ ⋈ []ₗ = Γ
Γ ⋈ (X ∷ₗ Δ) = (Γ ∷ ⟨ X ⟩) ⋈ Δ


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED EVALUATION CONTEXT

hole-ty-e : Γ ⊢E[ Δb ]⦂ X → Type
hole-ty-e {X = X} [-] = X
hole-ty-e (let= E `in M) = hole-ty-e E
hole-ty-e (↑ op V E) = hole-ty-e E
hole-ty-e (↓ op V E) = hole-ty-e E
hole-ty-e (promise op ↦ M `in E) = hole-ty-e E


-- FILLING A WELL-TYPED EVALUATION CONTEXT

{- LEMMA 3.5 -}

infix 30 _[_]
_[_] : (E : Γ ⊢E[ Δb ]⦂ X) → Γ ⋈ Δb ⊢M⦂ hole-ty-e E → Γ ⊢M⦂ X
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

strengthen-val : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A → Γ ⊢V⦂ ``` A
strengthen-val (` Tl x) = ` x
strengthen-val (`` c) = `` c


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

{- THEOREM 3.6 -}

infix 10 _↝_
data _↝_ : Γ ⊢M⦂ Y → Γ ⊢M⦂ Y → Set where

  -- COMPUTATIONAL RULES

  apply         : (M : Γ ∷ X ⊢M⦂ Y)
                  (V : Γ ⊢V⦂ X) →
                  ------------
                  ƛ M · V
                  ↝
                  M [ id-subst [ V ]s ]m

  let-return    : (V : Γ ⊢V⦂ X)
                  (N : Γ ∷ X ⊢M⦂ Y) →
                  ----------------
                  let= return V `in N
                  ↝
                  N [ id-subst [ V ]s ]m

  let-↑         : (N : Γ ∷ X ⊢M⦂ Y)
                  (V : Γ ⊢V⦂ ```(payload op))
                  (M : Γ ⊢M⦂ X) →
                  ------------
                  let= ↑ op V M `in N
                  ↝
                  ↑ op V (let= M `in N)

  ↓-↑           : (V' : Γ ⊢V⦂ ```(payload op'))
                  (V : Γ ⊢V⦂ ```(payload op))
                  (M : Γ ⊢M⦂ X) →
                  -------------------
                  ↓ op' V' (↑ op V M)
                  ↝
                  ↑ op V (↓ op' V' M)

  promise-↑     : (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op'))
                  (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                  (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                  ----------------------------
                  promise op ↦ M `in (↑ op' V N)
                  ↝
                  ↑ op' (strengthen-val V) (promise op ↦ M `in N)

  ↓-return      : (V : Γ ⊢V⦂ ```(payload op))
                  (W : Γ ⊢V⦂ Y) →
                  ------------
                  ↓ op V (return W)
                  ↝
                  return W

  let-promise   : (L : Γ ∷ Y ⊢M⦂ Z)
                  (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                  (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                  --------------------------------
                  let= promise op ↦ M `in N `in L
                  ↝
                  promise op ↦ M `in let= N `in M-rename (wk₂ wk₁) L

  ↓-promise-op  : (V : Γ ⊢V⦂ ```(payload op))
                  (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                  (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                  -------------------------------
                  ↓ op V (promise op ↦ M `in N)
                  ↝
                  let= M [ id-subst [ V ]s ]m `in ↓ op (V-rename wk₁ V) N

  ↓-promise-op' : (p : op ≢ op')
                  (V : Γ ⊢V⦂ ```(payload op'))
                  (M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩)
                  (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                  -------------------------------
                  ↓ op' V (promise op ↦ M `in N)
                  ↝
                  promise op ↦ M `in ↓ op' (V-rename wk₁ V) N

  let-await     : (N : Γ ∷ Y ⊢M⦂ Z) 
                  (V : Γ ⊢V⦂ ⟨ X ⟩)
                  (M : Γ ∷ X ⊢M⦂ Y) →
                  ----------------
                  let= await V until M `in N
                  ↝
                  await V until let= M `in M-rename (wk₂ wk₁) N

  ↓-await       : (W : Γ ⊢V⦂ ```(payload op))
                  (V : Γ ⊢V⦂ ⟨ X ⟩)
                  (M : Γ ∷ X ⊢M⦂ Y) →
                  ----------------
                  ↓ op W (await V until M)
                  ↝
                  await V until ↓ op (V-rename wk₁ W) M

  await-promise : (V : Γ ⊢V⦂ X)
                  (M : Γ ∷ X ⊢M⦂ Y) →
                  ----------------
                  await ⟨ V ⟩ until M
                  ↝
                  M [ id-subst [ V ]s ]m

  -- EVALUATION CONTEXT RULE

  context       : (E : Γ ⊢E[ Δb ]⦂ X)
                  {M N : Γ ⋈ Δb ⊢M⦂ hole-ty-e E} →
                  M ↝ N →
                  -----------------
                  E [ M ] ↝ E [ N ]