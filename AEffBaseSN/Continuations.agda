open import AEffBaseSN.AEffBase.Types
open import AEffBaseSN.AEffBase.AEff
open import AEffBaseSN.AEffBase.Renamings
open import AEffBaseSN.AEffBase.Finality
open import AEffBaseSN.SubstitutionProperties

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Function.Base using (_∘_)

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

module AEffBaseSN.Continuations where

-- WELL-TYPED CONTINUATIONS

infixl 20 _∘l_ _∘↓_[_]
data _⊢K⦂_⊸_ (Γ : Ctx) (X : Type) : Type → Set where

  id      : -----------
            Γ ⊢K⦂ X ⊸ X

  _∘l_    : Γ ⊢K⦂ Y ⊸ Z →
            Γ ∷ X ⊢M⦂ Y →
            -----------
            Γ ⊢K⦂ X ⊸ Z

  _∘↓_[_] : Γ ⊢K⦂ X ⊸ Z →
            (op : Σₛ) →
            Γ ⊢V⦂ ```(payload op) →
            -----------
            Γ ⊢K⦂ X ⊸ Z


-- ACTION OF CONTINUATIONS ON TERMS

infix 12 _aₖ_
_aₖ_ : Γ ⊢K⦂ X ⊸ Y → Γ ⊢M⦂ X → Γ ⊢M⦂ Y
id aₖ M = M
K ∘l N aₖ M = K aₖ let= M `in N
K ∘↓ op [ V ] aₖ M = K aₖ ↓ op V M


-- INDUCTIVE TYPE DESCRIBING HOW CONTINUATION APPLICATION INTERACTS WITH REDUCTION
-- AND PROOF OF ITS CORRECTNESS

infix 10 _`aₖ_↝↝_
data _`aₖ_↝↝_ : Γ ⊢K⦂ X ⊸ Y → Γ ⊢M⦂ X → Γ ⊢M⦂ Y → Set where

  ↝id : M ↝↝ M' →
        --------------
        id `aₖ M ↝↝ M'

  ↝∘l : (K : Γ ⊢K⦂ Y ⊸ Z) →
        let= M `in N ↝↝ L →
        ----------------------
        K ∘l N `aₖ M ↝↝ K aₖ L

  ↝∘↓ : (K : Γ ⊢K⦂ X ⊸ Z) →
        ↓ op V M ↝↝ L →
        -----------------------------
        K ∘↓ op [ V ] `aₖ M ↝↝ K aₖ L

aₖ→`aₖ : (K : Γ ⊢K⦂ X ⊸ Y) → K aₖ M ↝↝ N → K `aₖ M ↝↝ N
aₖ→`aₖ id r = ↝id r
aₖ→`aₖ (K ∘l N) r with aₖ→`aₖ K r
... | ↝id r = ↝∘l id r
... | ↝∘l _ (context-let r) = ↝∘l K r
... | ↝∘↓ _ (context-↓ r) = ↝∘l K r
aₖ→`aₖ (K ∘↓ op [ V ]) r with aₖ→`aₖ K r
... | ↝id _ = ↝∘↓ id r
... | ↝∘l _ (context-let r) = ↝∘↓ K r
... | ↝∘↓ _ (context-↓ r) = ↝∘↓ K r


-- REDUCTION CAN HAPPEN UNDER CONTINUATIONS

context-K : (K : Γ ⊢K⦂ X ⊸ Y) → M ↝↝ M' → K aₖ M ↝↝ K aₖ M'
context-K id r = r
context-K (K ∘l N) r = context-K K (context-let r)
context-K (K ∘↓ op [ V ]) r = context-K K (context-↓ r)


-- RENAMING OF CONTINUATIONS

K-rename : Ren Γ Γ' → Γ ⊢K⦂ X ⊸ Y → Γ' ⊢K⦂ X ⊸ Y
K-rename r id = id
K-rename r (K ∘l N) = K-rename r K ∘l M-rename (wk₂ r) N
K-rename r (K ∘↓ op [ V ]) = K-rename r K ∘↓ op [ V-rename r V ]


-- ACTION OF IDENTITY RENAMINGS LEAVES THE CONTINUATION UNCHANGED

ren-id-k : (K : Γ ⊢K⦂ X ⊸ Y) → K-rename id-ren K ≡ K
ren-id-k id = refl
ren-id-k (K ∘l M) = cong₂ _∘l_ (ren-id-k K) ren-id-l
ren-id-k (K ∘↓ op [ V ]) = cong₂ (_∘↓ op [_]) (ren-id-k K) ren-id-v


-- ACTION OF A COMPOSITION OF RENAMINGS IS THE SAME AS PERFORMING THE RENAMINGS ONE AFTER THE OTHER

ren-ren-k : (K : Γ ⊢K⦂ X ⊸ Y) → K-rename r (K-rename r' K) ≡ K-rename (r ∘ r') K
ren-ren-k id = refl
ren-ren-k (K ∘l N) = cong₂ _∘l_ (ren-ren-k K) ren-ren-l
ren-ren-k (K ∘↓ op [ V ]) = cong₂ (_∘↓ op [_]) (ren-ren-k K) ren-ren-v