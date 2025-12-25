open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; s≤s; _<_; ≤-pred)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (≤-refl; +-monoˡ-<; +-monoʳ-<; +-mono-≤; +-mono-<-≤; +-mono-≤-<)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (List) renaming (_∷_ to _∷ₗ_; [] to []ₗ; [_] to [_]ₗ)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Function using (_∘_)

open import AEffFinSN.AEffFin
open import AEffFinSN.FiniteEffectAnnotations

open import EffectAnnotations using (Σₛ)
open import AEff using (payload)

module AEffFinSN.SN where

variable
  n m k l : ℕ

#↑ : Γ ⊢M⦂ C → ℕ
#↑ (↑ _ _ M) = suc (#↑ M)
#↑ _ = 0

data SNₚ (P : Γ ⊢P⦂) : Set where
  sn : ({Q : Γ ⊢P⦂} → P ↝ₚ Q → SNₚ Q) → SNₚ P

data SN (M : Γ ⊢M⦂ C) (n : ℕ) : ℕ → Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝ N → SN N n m) → #↑ M ≤ n → SN M n (suc m)

postulate
  ≡-↓-sn : ¬ [ op ]ₗ ∈ᵢ i-of (type-of M) → SN M n m → Σ[ m ∈ ℕ ] SN (↓ op V M) n m
  strong-norm : (M : Γ ⊢M⦂ C) → Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] SN M n m

ΣSN : Γ ⊢M⦂ C → Set
ΣSN M = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] SN M n m

sn-strip-↑ : SN (↑ op V M) (suc n) m → SN M n m
sn-strip-↑ (sn sM le) = sn (λ r → sn-strip-↑ (sM (context-↑ r))) (≤-pred le)

sn* : Γ ⊢P⦂ → Set
sn* [] = ⊤
sn* (M ∥ P) = ΣSN M × sn* P

sn-↓ : (op : Σₛ) (V : Γ ⊢V⦂ ```(payload op)) → ΣSN M → ΣSN (↓ op V M)
sn-↓ {M = M} op V (_ , _ , sM) with [ op ]ₗ ∈ᵢ? i-of (type-of M)
... | yes _ = strong-norm _
... | no  a = _ , ≡-↓-sn a sM

sn*-↓ₜ : (op : Σₛ) (V : Γ ⊢V⦂ ```(payload op)) → sn* P → sn* (↓ₜ op V P)
sn*-↓ₜ {P = []} _ _ sP = tt
sn*-↓ₜ {P = _ ∥ _} _ _ (sM , sP) = sn-↓ _ _ sM , sn*-↓ₜ _ _ sP

sn*-run : P ↝ₚ-↝ Q → sn* P → sn* Q
sn*-run (context-∥ₗ r) ((_ , _ , sn f _) , sP) = (_ , _ , f r) , sP
sn*-run (context-∥ᵣ r) (sM , sP) = sM , sn*-run r sP

sn*-↑-∥ : P ↝ₚ-[ op , V ] Q → sn* P → sn* Q
sn*-↑-∥ ↑-∥ₗ ((suc _ , _ , sn sM le) , sP) = (_ , _ , sn-strip-↑ (sn sM le)) , sn*-↓ₜ _ _ sP
sn*-↑-∥ (↑-∥ᵣ r) (sM , sP) = sn-↓ _ _ sM , sn*-↑-∥ r sP

sn*-↝ : P ↝ₚ Q → sn* P → sn* Q
sn*-↝ (↑-∥ r) sP = sn*-↑-∥ r sP
sn*-↝ (run r) sP = sn*-run r sP

∣_∣ₘ : Γ ⊢M⦂ C → ℕ
∣ M ∣ₘ = ∣ isf-of (type-of M) ∣

∣_∣↑ : sn* P → ℕ
∣_∣↑ {P = []} _ = 0
∣_∣↑ {P = _ ∥ _} ((n , _) , sP) = n + ∣ sP ∣↑

∣_∣i : sn* P → ℕ
∣_∣i {P = []} _ = 0
∣_∣i {P = M ∥ _} (_ , sP) = ∣ M ∣ₘ + ∣ sP ∣i

∣_∣↝ : sn* P → ℕ
∣_∣↝ {P = []} _ = 0
∣_∣↝ {P = _ ∥ _} ((_ , m , _) , sP) = m + ∣ sP ∣↝

run-↝-< : {P : Γ ⊢P⦂} (r : P ↝ₚ-↝ Q) (sP : sn* P) → ∣ sn*-run r sP ∣↝ < ∣ sP ∣↝
run-↝-< (context-∥ₗ r) ((_ , _ , sn _ _) ,  _) = ≤-refl
run-↝-< (context-∥ᵣ r) ( _ , sP) = +-monoʳ-< _ (run-↝-< r sP)

run-i-≡ : {P : Γ ⊢P⦂} (r : P ↝ₚ-↝ Q) (sP : sn* P) → ∣ sn*-run r sP ∣i ≡ ∣ sP ∣i
run-i-≡ (context-∥ₗ r) (_ ,  _) = refl
run-i-≡ (context-∥ᵣ r) (_ , sP) = cong (_ +_) (run-i-≡ r sP)

run-↑-≡ : {P : Γ ⊢P⦂} (r : P ↝ₚ-↝ Q) (sP : sn* P) → ∣ sn*-run r sP ∣↑ ≡ ∣ sP ∣↑
run-↑-≡ (context-∥ₗ r) ((_ , _ , sn _ _) ,  _) = refl
run-↑-≡ (context-∥ᵣ r) ( _ , sP) = cong (_ +_) (run-↑-≡ r sP)

has : Σₛ → Γ ⊢P⦂ → Set
has op [] = ⊥
has op (M ∥ P) = [ op ]ₗ ∈ᵢ i-of (type-of M) ⊎ has op P

has? : (op : Σₛ) (P : Γ ⊢P⦂) → Dec (has op P)
has? op [] = no (λ ())
has? op (M ∥ P) with [ op ]ₗ ∈ᵢ? i-of (type-of M)
... | yes a = yes (inj₁ a)
... | no  a with has? op P
...   | yes a = yes (inj₂ a)
...   | no  b = no (λ {(inj₁ x) → a x; (inj₂ y) → b y})

module _ (op : Σₛ) (V : Γ ⊢V⦂ ```(payload op)) where

  ∣∣ₘ-↓-≤ : (M : Γ ⊢M⦂ C) → ∣ ↓ op V M ∣ₘ ≤ ∣ M ∣ₘ
  ∣∣ₘ-↓-≤ M = size-↓ₑ-≤ (isf-of (type-of M))

  ∣∣ₘ-↓-< : (M : Γ ⊢M⦂ C) → [ op ]ₗ ∈ᵢ i-of (type-of M) → ∣ ↓ op V M ∣ₘ < ∣ M ∣ₘ
  ∣∣ₘ-↓-< M = size-↓ₑ-< (isf-of (type-of M))

  ∣∣ₘ-↓-≡ : (M : Γ ⊢M⦂ C) → ¬ [ op ]ₗ ∈ᵢ i-of (type-of M) → ∣ ↓ op V M ∣ₘ ≡ ∣ M ∣ₘ
  ∣∣ₘ-↓-≡ M h = size-↓ₑ-≡ (isf-of (type-of M)) h

  sn*-↓ₜ-i-≤ : {P : Γ ⊢P⦂} (sP : sn* P) → ∣ sn*-↓ₜ op V sP ∣i ≤ ∣ sP ∣i
  sn*-↓ₜ-i-≤ {P = []} sP = z≤n
  sn*-↓ₜ-i-≤ {P = M ∥ P} (_ , sP) = +-mono-≤ (∣∣ₘ-↓-≤ M) (sn*-↓ₜ-i-≤ sP)

  sn*-↓ₜ-i-< : {P : Γ ⊢P⦂} (sP : sn* P) → has op P → ∣ sn*-↓ₜ op V sP ∣i < ∣ sP ∣i
  sn*-↓ₜ-i-< {P = M ∥ P} (_ , sP) (inj₁ h) = +-mono-<-≤ (∣∣ₘ-↓-< M h) (sn*-↓ₜ-i-≤ sP)
  sn*-↓ₜ-i-< {P = M ∥ P} (_ , sP) (inj₂ h) = +-mono-≤-< (∣∣ₘ-↓-≤ M) (sn*-↓ₜ-i-< sP h)

  sn*-↓ₜ-i-≡ : {P : Γ ⊢P⦂} (sP : sn* P) → ¬ has op P → ∣ sn*-↓ₜ op V sP ∣i ≡ ∣ sP ∣i
  sn*-↓ₜ-i-≡ {P = []} sP h = refl
  sn*-↓ₜ-i-≡ {P = M ∥ P} (sM , sP) h with [ op ]ₗ ∈ᵢ? i-of (type-of M)
  ... | yes a = ⊥-elim (h (inj₁ a))
  ... | no  a rewrite sym (∣∣ₘ-↓-≡ M a) = cong (_ +_) (sn*-↓ₜ-i-≡ sP (h ∘ inj₂))

  sn*-↓ₜ-↑-≡ : {P : Γ ⊢P⦂} (sP : sn* P) → ¬ has op P → ∣ sn*-↓ₜ op V sP ∣↑ ≡ ∣ sP ∣↑
  sn*-↓ₜ-↑-≡ {P = []} sP hP = refl
  sn*-↓ₜ-↑-≡ {P = M ∥ P} (sM , sP) h with [ op ]ₗ ∈ᵢ? i-of (type-of M)
  ... | yes a = ⊥-elim (h (inj₁ a))
  ... | no  a = cong (_ +_) (sn*-↓ₜ-↑-≡ sP (h ∘ inj₂))

  ↑-∥-i-< : (r : P ↝ₚ-[ op , V ] Q)
            (sP : sn* P) →
            ---------------------------------------------------------
            ∣ sn*-↑-∥ r sP ∣i < ∣ sP ∣i
            ⊎
            ∣ sn*-↑-∥ r sP ∣i ≡ ∣ sP ∣i × ∣ sn*-↑-∥ r sP ∣↑ < ∣ sP ∣↑
  ↑-∥-i-< (↑-∥ₗ {M = M} {P = P}) ((suc _ , _ , sn _ _) , sP) with has? op P
  ... | yes a = inj₁ (+-monoʳ-< _ (sn*-↓ₜ-i-< sP a))
  ... | no  a rewrite sym (sn*-↓ₜ-↑-≡ sP a) = inj₂ (cong (_ +_) (sn*-↓ₜ-i-≡ sP a) , ≤-refl)
  ↑-∥-i-< (↑-∥ᵣ {M = M} r) (sM , sP) with ↑-∥-i-< r sP
  ... | inj₁ le = inj₁ (+-mono-≤-< (∣∣ₘ-↓-≤ M) le)
  ... | inj₂ (eq , le) with [ op ]ₗ ∈ᵢ? i-of (type-of M)
  ...   | yes a rewrite eq = inj₁ (+-monoˡ-< _ (∣∣ₘ-↓-< M a))
  ...   | no  a rewrite eq = inj₂ (cong (_+ _) (∣∣ₘ-↓-≡ M a) , +-monoʳ-< _ le)

strong-normₚ' : (sP : sn* P) →
                Acc _<_ ∣ sP ∣i →
                Acc _<_ ∣ sP ∣↑ →
                Acc _<_ ∣ sP ∣↝ →
                ---------------------------
                {Q : Γ ⊢P⦂} → P ↝ₚ Q → SNₚ Q
strong-normₚ' sP _ _ _ (↑-∥ r) with ↑-∥-i-< _ _ r sP
strong-normₚ' sP (acc ai) _ _ (↑-∥ r)  | inj₁ le = sn (strong-normₚ' (sn*-↑-∥ r sP) (ai le) (<-wellFounded _) (<-wellFounded _))
strong-normₚ' sP ai (acc a↑) _ (↑-∥ r) | inj₂ (eq , le) rewrite sym eq = sn (strong-normₚ' _ ai (a↑ le) (<-wellFounded _))
strong-normₚ' sP ai a↑ (acc a↝) (run r)
  rewrite sym (run-i-≡ r sP) | sym (run-↑-≡ r sP) =
  sn (strong-normₚ' _ ai a↑ (a↝ (run-↝-< r sP)))

all-sn* : (P : Γ ⊢P⦂) → sn* P
all-sn* [] = tt
all-sn* (M ∥ P) = strong-norm M , all-sn* P

strong-normₚ : (P : Γ ⊢P⦂) → SNₚ P
strong-normₚ P = sn (strong-normₚ' (all-sn* P) (<-wellFounded _) (<-wellFounded _) (<-wellFounded _))