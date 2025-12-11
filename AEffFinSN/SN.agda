open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Nat.Properties
open import Data.List using (List) renaming (_∷_ to _∷ₗ_; [] to []ₗ)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Binary.PropositionalEquality

open import AEffFinSN.AEffFin
open import AEffFinSN.FiniteEffectAnnotations

open import EffectAnnotations using (Σₛ)
open import AEff using (payload; Σ-base; ar-base)
open import Types using (GType)

module AEffFinSN.SN where

variable
  n m k l : ℕ

_⊢I⦂ : Ctx Γs → Set
Γ ⊢I⦂ = List (Σ[ op ∈ Σₛ ] Γ ⊢V⦂ ```(payload op))

ops-⊢I : Γ ⊢I⦂ → List Σₛ
ops-⊢I []ₗ = []ₗ
ops-⊢I ((op , _) ∷ₗ I) = op ∷ₗ ops-⊢I I

_aI_ : (I : Γ ⊢I⦂) → Γ ⊢M⦂ X ! (i , isf) → Γ ⊢M⦂ X ! (ops-⊢I I ↓↓ₑ i , fin-↓↓ₑ (ops-⊢I I) isf)
[]ₗ aI M = M
((op , V) ∷ₗ I) aI M = I aI (↓ op V M)

_aIₚ_ : (I : Γ ⊢I⦂) → Γ ⊢P⦂ PP → Γ ⊢P⦂ (ops-⊢I I ↓↓ₚ PP)
[]ₗ aIₚ P = P
((op , V) ∷ₗ I) aIₚ P = I aIₚ (↓ op V P)

data _`aIₚ_`↝ₚ_ : Γ ⊢I⦂ → Γ ⊢P⦂ PP → Γ ⊢P⦂ QQ → Set where

  `id : P ↝ₚ P' →
        -------------
        []ₗ `aIₚ P `↝ₚ P'

  `aI : (I : Γ ⊢I⦂) →
        ↓ op V P ↝ₚ Q →
        -------------------------
        ((op , V) ∷ₗ I) `aIₚ P `↝ₚ (I aIₚ Q)

context-Iₚ : (I : Γ ⊢I⦂) → P ↝ₚ P' → I aIₚ P ↝ₚ I aIₚ P'
context-Iₚ []ₗ r = r
context-Iₚ (_ ∷ₗ I) r = context-Iₚ I (context-↓ r)

context-I : (I : Γ ⊢I⦂) → M ↝ M' → I aI M ↝ I aI M'
context-I []ₗ r = r
context-I (_ ∷ₗ I) r = context-I I (context-↓ r)

aIₚ→`aIₚ : (I : Γ ⊢I⦂) →
           I aIₚ P ↝ₚ Q →
           ---------------
           I `aIₚ P `↝ₚ Q
aIₚ→`aIₚ []ₗ r = `id r
aIₚ→`aIₚ (_ ∷ₗ I) r with aIₚ→`aIₚ I r
... | `id _ = `aI []ₗ r
... | `aI _ (context-↓ r) = `aI _ r

#↑ : Γ ⊢M⦂ C → ℕ
#↑ (↑ _ _ M) = 1 + #↑ M
#↑ _ = 0

#↑ₚ : Γ ⊢P⦂ PP → ℕ
#↑ₚ (↑ _ _ P) = 1 + #↑ₚ P
#↑ₚ _ = 0

data SNₚ (P : Γ ⊢P⦂ PP) : Set where
  sn : ({QQ : PType} {Q : Γ ⊢P⦂ QQ} → P ↝ₚ Q → SNₚ Q) → SNₚ P

data SN↑ (M : Γ ⊢M⦂ C) (n : ℕ) : Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝ N → SN↑ N n) → #↑ M ≤ n → SN↑ M n

data SN↑ₚ (P : Γ ⊢P⦂ PP) (n : ℕ) : Set where
  sn : ({QQ : PType} {Q : Γ ⊢P⦂ QQ} → P ↝ₚ Q → SN↑ₚ Q n) → #↑ₚ P ≤ n → SN↑ₚ P n

SN↑ₚ' : Γ ⊢P⦂ PP → ℕ → Set
SN↑ₚ' P n = {QQ : PType} {Q : _ ⊢P⦂ QQ} → P ↝ₚ Q → SN↑ₚ Q n

sn↑ₚ'→sn↑ₚ : SN↑ₚ' P n × #↑ₚ P ≤ n → SN↑ₚ P n
sn↑ₚ'→sn↑ₚ (s , le) = sn s le

sn↑ₚ→sn↑ₚ' : SN↑ₚ P n → SN↑ₚ' P n
sn↑ₚ→sn↑ₚ' (sn f le) = f

sn↑ₚ→#↑ₚ≤ : SN↑ₚ P n → #↑ₚ P ≤ n
sn↑ₚ→#↑ₚ≤ (sn _ le) = le

#↑ₚ-↓ : (I : Γ ⊢I⦂) → #↑ₚ (I aIₚ ↓ op V P) ≡ 0
#↑ₚ-↓ []ₗ = refl
#↑ₚ-↓ (_ ∷ₗ I) = #↑ₚ-↓ I

#↑ₚ-↑ : (I : Γ ⊢I⦂) → #↑ₚ (I aIₚ P) ≤ n → #↑ₚ (I aIₚ ↑ op V P) ≤ suc n
#↑ₚ-↑ []ₗ le = s≤s le
#↑ₚ-↑ (_ ∷ₗ I) le = ≤-trans (≤-reflexive (#↑ₚ-↓ I)) z≤n

sn↑ₚ-↑' : (I : Γ ⊢I⦂) → SN↑ₚ (I aIₚ P) n → SN↑ₚ' (I aIₚ (↑ op V P)) (suc n)
sn↑ₚ-↑' I (sn sP le) r with aIₚ→`aIₚ I r
... | `id (context-↑ r) = sn↑ₚ'→sn↑ₚ (sn↑ₚ-↑' []ₗ (sP r) , s≤s (sn↑ₚ→#↑ₚ≤ (sP r)))
... | `aI I (↓-↑ V W P) = sn↑ₚ'→sn↑ₚ (sn↑ₚ-↑' I (sn sP le) , #↑ₚ-↑ I le)
... | `aI _ (context-↓ (context-↑ r)) = sn↑ₚ'→sn↑ₚ (sn↑ₚ-↑' I (sP (context-Iₚ I r)) , #↑ₚ-↑ I (sn↑ₚ→#↑ₚ≤ (sP (context-Iₚ I r))))

sn↑ₚ-↑ : (I : Γ ⊢I⦂) → SN↑ₚ (I aIₚ P) n → SN↑ₚ (I aIₚ (↑ op V P)) (suc n)
sn↑ₚ-↑ I sP@(sn _ le) = sn (sn↑ₚ-↑' I sP) (#↑ₚ-↑ I le)

i-of : PType → I
i-of (```` _ ! (i , _)) = i
i-of (PP ∥ QQ) = i-of PP ∪ i-of QQ

isf-of : (PP : PType) → isfin (i-of PP)
isf-of (```` _ ! (_ , isf)) = isf
isf-of (PP ∥ QQ) = fin-∪ (isf-of PP) (isf-of QQ)

∣_∣ₚₚ : PType → ℕ
∣ PP ∣ₚₚ = ∣ isf-of PP ∣

comm-↓ₑ-i-of₁ : (PP : PType) → op ↓ₑ i-of PP ⊑i i-of (op ↓ₚ PP)
comm-↓ₑ-i-of₁ (```` _ ! (_ , _)) = ⊑i-refl
comm-↓ₑ-i-of₁ (PP ∥ QQ) =
  ⊑i-trans
    (↓ₑ-distrib-∪₁ {_} {i-of PP})
    (∪-copair (⊑i-trans (comm-↓ₑ-i-of₁ PP) ∪-inl) (⊑i-trans (comm-↓ₑ-i-of₁ QQ) ∪-inr))

comm-↓ₑ-i-of₂ : (PP : PType) → i-of (op ↓ₚ PP) ⊑i op ↓ₑ i-of PP
comm-↓ₑ-i-of₂ (```` _ ! (_ , _)) = ⊑i-refl
comm-↓ₑ-i-of₂ (PP ∥ QQ) =
  ∪-copair
    (⊑i-trans (comm-↓ₑ-i-of₂ PP) (↓ₑ-mono {i-of PP} ∪-inl))
    (⊑i-trans (comm-↓ₑ-i-of₂ QQ) (↓ₑ-mono {i-of QQ} {i-of PP ∪ i-of QQ} ∪-inr))

size-↓ₚ : (PP : PType) → ∣ fin-↓ₑ op (isf-of PP) ∣ ≡ ∣ isf-of (op ↓ₚ PP) ∣
size-↓ₚ PP = ≤-antisym (size-⊑i _ _ (comm-↓ₑ-i-of₁ PP)) (size-⊑i _ _ (comm-↓ₑ-i-of₂ PP))

size-↓ₑ-↓ₚ : (PP : PType) → ∣ op ↓ₚ PP ∣ₚₚ ≤ ∣ PP ∣ₚₚ
size-↓ₑ-↓ₚ {op} PP rewrite sym (size-↓ₚ {op} PP) = size-↓ₑ (isf-of PP)

sn-strip-↑ : SN↑ₚ (↑ op V P) (suc n) → SN↑ₚ P n
sn-strip-↑ (sn sP le) = sn (λ r → sn-strip-↑ (sP (context-↑ r))) (≤-pred le)

ProcRed : Γ ⊢P⦂ PP → Set
ProcRed P = (I : _ ⊢I⦂) → SNₚ (I aIₚ P)

snₚ-∥ : {P : Γ ⊢P⦂ PP} {Q : Γ ⊢P⦂ QQ}
        (I : Γ ⊢I⦂) →
        Acc _<_ ∣ PP ∣ₚₚ →
        Acc _<_ ∣ QQ ∣ₚₚ →
        ProcRed P →
        ProcRed Q →
        SN↑ₚ (I aIₚ P) k →
        SN↑ₚ (I aIₚ Q) l →
        --------------------
        SN↑ₚ' (I aIₚ (P ∥ Q)) (k + l)
snₚ-∥ I p q rP rQ sP sQ r with aIₚ→`aIₚ I r
snₚ-∥ {k = zero} I p q rP rQ sP sQ r | `id (↑-∥ₗ V P Q) = {! impossible  !}
snₚ-∥ {QQ = QQ} {k = suc k} {P = P} {Q} I p (acc aQ) rP rQ sP sQ r | `id (↑-∥ₗ {op = op} V P' Q') =
  sn↑ₚ-↑ []ₗ
    ([
      (λ op↓ₚQQ<QQ → snₚ-∥ {Q = ↓ op V Q} []ₗ p (aQ op↓ₚQQ<QQ) _ _
        (sn-strip-↑ sP) _ {!   !}) ,
      {!   !}
    ]′ (m≤n⇒m<n∨m≡n (size-↓ₑ-↓ₚ {op} QQ)))
snₚ-∥ I p q rP rQ sP sQ r | `id (↑-∥ᵣ V P Q) = {!   !}
snₚ-∥ I p q rP rQ sP sQ r | `id (context-∥ₗ x) = {!   !}
snₚ-∥ I p q rP rQ sP sQ r | `id (context-∥ᵣ x) = {!   !}
snₚ-∥ I p q rP rQ sP sQ r | `aI I₁ x = {!   !}