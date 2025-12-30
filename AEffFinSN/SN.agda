open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; s≤s; _<_; ≤-pred)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoˡ-<; +-monoʳ-<; +-mono-≤; +-mono-<-≤; +-mono-≤-<; +-suc)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (List) renaming (_∷_ to _∷ₗ_; [] to []ₗ; [_] to [_]ₗ)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

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

data SN↑ (M : Γ ⊢M⦂ C) (n : ℕ) : Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝ N → SN↑ N n) → #↑ M ≤ n → SN↑ M n

ΣSN : Γ ⊢M⦂ C → Set
ΣSN M = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] SN M n m

postulate
  strong-norm : (M : Γ ⊢M⦂ C) → ΣSN M
  sn↑-sn : SN↑ M n → Σ[ m ∈ ℕ ] SN M n m

sn-sn↑ : SN M n m → SN↑ M n
sn-sn↑ (sn sM le) = sn (λ x → sn-sn↑ (sM x)) le

sn-#↑ : SN↑ M n → #↑ M ≤ n
sn-#↑ (sn _ le) = le

data Form {op} {i} {isf} : Γ ⊢M⦂ X ! (i , isf) → Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf) → Set where
  [-]     : Form M (↓ op V M)
  return  : Form (return V) (return V)
  ↑       : Form M N → Form (↑ op' V M) (↑ op' V N)
  await   : Form M N → Form (await V until M) (await V until N)
  promise : ∀ {x y x' y'} → Form M N → Form (promise op' ∣ x , y ↦ L `in M) (promise op' ∣ x' , y' ↦ L `in N)

form-sub : {M : Γ ⊢M⦂ X ! (i , isf)}
           {N : Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf)}
           (s : Sub Γ Γ') →
           Form M N →
           --------------------------
           Form (M [ s ]m) (N [ s ]m)
form-sub s [-] = [-]
form-sub s return = return
form-sub s (↑ ff) = ↑ (form-sub _ ff)
form-sub s (await ff) = await (form-sub _ ff)
form-sub s (promise ff) = promise (form-sub _ ff)

form-↝ : {M : Γ ⊢M⦂ X ! (i , isf)}
         {N : Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf)} →
         ¬ [ op ]ₗ ∈ᵢ i →
         Form M N →
         N ↝ N' →
         ----------------------------
         Form M N' ⊎ Σ[ M' ∈ _ ] Form M' N' × M ↝ M'
form-↝ u [-] (↓-return V W) = inj₁ return
form-↝ u [-] (↓-↑ V W M) = inj₁ (↑ [-])
form-↝ u [-] (↓-promise-op p q V M N) = ⊥-elim (u q)
form-↝ u [-] (↓-promise-op' V p q r M N) = inj₁ (promise [-])
form-↝ u [-] (↓-await W V M) = inj₁ (await [-])
form-↝ u [-] (context-↓ r) = inj₂ (_ , [-] , r)
form-↝ u (↑ ff) (context-↑ r) with form-↝ u ff r
... | inj₁ ff = inj₁ (↑ ff)
... | inj₂ (_ , ff , r) = inj₂ (_ , ↑ ff , context-↑ r)
form-↝ u (await ff) (await-promise V N) = inj₂ (_ , form-sub _ ff , await-promise V _)
form-↝ u (promise (↑ ff)) (promise-↑ p q V M N) = inj₂ (_ , ↑ (promise ff) , promise-↑ _ _ _ _ _)
form-↝ u (promise ff) (context-promise r) with form-↝ u ff r
... | inj₁ ff = inj₁ (promise ff)
... | inj₂ (_ , ff , r) = inj₂ (_ , promise ff , context-promise r)

form-#↑ : Form M N → #↑ N ≤ #↑ M
form-#↑ [-] = z≤n
form-#↑ return = z≤n
form-#↑ (↑ ff) = s≤s (form-#↑ ff)
form-#↑ (await ff) = z≤n
form-#↑ (promise ff) = z≤n

≡-↓-sn' : {M : Γ ⊢M⦂ X ! (i , isf)}
          {N : Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf)} →
          ¬ [ op ]ₗ ∈ᵢ i →
          SN↑ M n →
          SN↑ N m →
          Form M N →
          --------------------------
          ∀ {N'} → N ↝ N' → SN↑ N' n
≡-↓-sn' u (sn sM le) (sn sN le') ff r with form-↝ u ff r
... | inj₁ ff = sn (≡-↓-sn' u (sn sM le) (sN r) ff) (≤-trans (form-#↑ ff) le)
... | inj₂ (_ , ff , r') = sn (≡-↓-sn' u (sM r') (sN r) ff) (≤-trans (form-#↑ ff) (sn-#↑ (sM r')))

≡-↓-sn : ¬ [ op ]ₗ ∈ᵢ i-of (type-of M) → SN↑ M n → SN↑ (↓ op V M) n
≡-↓-sn {_} {_} {_ ! _} u s = sn (≡-↓-sn' u s (sn-sn↑ (proj₂ (proj₂ (strong-norm _)))) [-]) z≤n

sn-strip-↑ : SN (↑ op V M) (suc n) m → SN M n m
sn-strip-↑ (sn sM le) = sn (λ r → sn-strip-↑ (sM (context-↑ r))) (≤-pred le)

sn* : Γ ⊢P⦂ → Set
sn* [] = ⊤
sn* (M ∥ P) = ΣSN M × sn* P

sn-↓ : (op : Σₛ) (V : Γ ⊢V⦂ ```(payload op)) → ΣSN M → ΣSN (↓ op V M)
sn-↓ {M = M} op V (_ , _ , sM) with [ op ]ₗ ∈ᵢ? i-of (type-of M)
... | yes _ = strong-norm _
... | no  a = _ , sn↑-sn (≡-↓-sn a (sn-sn↑ sM))

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