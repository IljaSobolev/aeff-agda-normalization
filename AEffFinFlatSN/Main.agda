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

open import AEffFinFlatSN.AEffSequential
open import AEffFinFlatSN.AEffParallelFlat
open import AEffFinFlatSN.FiniteEffectAnnotations
open import AEffFinFlatSN.Simulation
open import AEffFinFlatSN.StronglyNormalising

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

module AEffFinFlatSN.Main where

-- INFIX-↓ M N SAYS ROUGHLY THAT M AND N ARE OF FORMS E [ L ] AND E [ ↓ op V L ] RESPECTIVELY

data Infix-↓ {op} {i} {isf} : Γ ⊢M⦂ X ! (i , isf) → Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf) → Set where
  [-]     : Infix-↓ M (↓ op V M)
  return  : Infix-↓ (return V) (return V)
  ↑       : Infix-↓ M N → Infix-↓ (↑ op' V M) (↑ op' V N)
  await   : Infix-↓ M N → Infix-↓ (await V until M) (await V until N)
  promise : ∀ {x y x' y'} → Infix-↓ M N → Infix-↓ (promise op' ∣ x , y ↦ L `in M) (promise op' ∣ x' , y' ↦ L `in N)

infix-↓-sub : {M : Γ ⊢M⦂ X ! (i , isf)}
              {N : Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf)}
              (s : Sub Γ Γ') →
              Infix-↓ M N →
              --------------------------
              Infix-↓ (M [ s ]m) (N [ s ]m)

infix-↓-sub s [-] = [-]
infix-↓-sub s return = return
infix-↓-sub s (↑ ff) = ↑ (infix-↓-sub _ ff)
infix-↓-sub s (await ff) = await (infix-↓-sub _ ff)
infix-↓-sub s (promise ff) = promise (infix-↓-sub _ ff)


-- IF M DOES NOT HAVE A HANDLER FOR AN INTERRUPT,
-- THEN ACTING WITH THAT INTERRUPT PRESERVES THE STRUCTURE OF M

infix-↓-↝ : {M : Γ ⊢M⦂ X ! (i , isf)}
            {N : Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf)} →
            ¬ [ op ]ₗ ∈ᵢ i →
            Infix-↓ M N →
            N ↝↝ N' →
            ----------------------------
            Infix-↓ M N' ⊎ Σ[ M' ∈ _ ] Infix-↓ M' N' × M ↝↝ M'

infix-↓-↝ u [-] (↓-return V W) = inj₁ return
infix-↓-↝ u [-] (↓-↑ V W M) = inj₁ (↑ [-])
infix-↓-↝ u [-] (↓-promise-op p q V M N) = ⊥-elim (u q)
infix-↓-↝ u [-] (↓-promise-op' V p q r M N) = inj₁ (promise [-])
infix-↓-↝ u [-] (↓-await W V M) = inj₁ (await [-])
infix-↓-↝ u [-] (context-↓ r) = inj₂ (_ , [-] , r)
infix-↓-↝ u (↑ ff) (context-↑ r) with infix-↓-↝ u ff r
... | inj₁ ff = inj₁ (↑ ff)
... | inj₂ (_ , ff , r) = inj₂ (_ , ↑ ff , context-↑ r)
infix-↓-↝ u (await ff) (await-promise V N) = inj₂ (_ , infix-↓-sub _ ff , await-promise V _)
infix-↓-↝ u (promise (↑ ff)) (promise-↑ p q V M N) = inj₂ (_ , ↑ (promise ff) , promise-↑ _ _ _ _ _)
infix-↓-↝ u (promise ff) (context-promise r) with infix-↓-↝ u ff r
... | inj₁ ff = inj₁ (promise ff)
... | inj₂ (_ , ff , r) = inj₂ (_ , promise ff , context-promise r)

infix-↓-#↑ : Infix-↓ M N → #↑ N ≤ #↑ M
infix-↓-#↑ [-] = z≤n
infix-↓-#↑ return = z≤n
infix-↓-#↑ (↑ ff) = s≤s (infix-↓-#↑ ff)
infix-↓-#↑ (await ff) = z≤n
infix-↓-#↑ (promise ff) = z≤n

≡-↓-sn' : {M : Γ ⊢M⦂ X ! (i , isf)}
          {N : Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf)} →
          ¬ [ op ]ₗ ∈ᵢ i →
          SN↑ M n →
          SN↑ N m →
          Infix-↓ M N →
          --------------------------
          ∀ {N'} → N ↝↝ N' → SN↑ N' n

≡-↓-sn' u (sn sM le) (sn sN le') ff r with infix-↓-↝ u ff r
... | inj₁ ff = sn (≡-↓-sn' u (sn sM le) (sN r) ff) (≤-trans (infix-↓-#↑ ff) le)
... | inj₂ (_ , ff , r') = sn (≡-↓-sn' u (sM r') (sN r) ff) (≤-trans (infix-↓-#↑ ff) (sn-#↑ (sM r')))


-- ACTING WITH AN INTERRUPT ON A TERM THAT HAS NO HANDLER FOR THAT INTERRUPT
-- DOES NOT INCREASE THE MAXIMUM NUMBER OF OUTGOING SIGNALS

≡-↓-sn : ¬ [ op ]ₗ ∈ᵢ i-of (type-of M) → SN↑ M n → SN↑ (↓ op V M) n
≡-↓-sn {_} {_} {_ ! _} u s = sn (≡-↓-sn' u s (sn→sn↑ (strong-norm _)) [-]) z≤n


-- INTRODUCING AN INTERRUPT PRESERVES STRONG NORMALISATION

sn-↓ : (op : Σₛ) (V : Γ ⊢V⦂ ```(payload op)) → ΣSN M → ΣSN (↓ op V M)
sn-↓ {M = M} op V (_ , _ , sM) with [ op ]ₗ ∈ᵢ? i-of (type-of M)
... | yes _ = strong-norm-Σ (strong-norm _)
... | no  a = _ , sn↑-sni↑ (≡-↓-sn a (sni↑→sn↑ sM))

-- REMOVING A SIGNAL PRESERVES STRONG NORMALISATION AND REDUCES MAXIMUM NUMBER OF OUTGOING SIGNALS

sn-strip-↑ : SNi↑ (↑ op V M) (suc n) m → SNi↑ M n m
sn-strip-↑ (sn sM le) = sn (λ r → sn-strip-↑ (sM (context-↑ r))) (≤-pred le)


-- DATATYPE EXPRESSING THAT EACH INDIVIDUAL COMPUTATION IN A PROCESS
-- IS STRONGLY NORMALISING IN ISOLATION,
-- AND ITS PROPERTIES

data sn* : Γ ⊢P⦂ → Set where
  run : ΣSN M → sn* (run M)
  _∥_ : ΣSN M → sn* P → sn* (M ∥ P)

sn*-↓ₜ : (op : Σₛ) (V : Γ ⊢V⦂ ```(payload op)) → sn* P → sn* (↓ₜ op V P)
sn*-↓ₜ _ _ (run sM) = run (sn-↓ _ _ sM)
sn*-↓ₜ _ _ (sM ∥ sP) = sn-↓ _ _ sM ∥ sn*-↓ₜ _ _ sP

sn*-run : P ↝↝ₚ-↝ Q → sn* P → sn* Q
sn*-run (run r) (run (_ , _ , sn f _)) = run (_ , _ , f r)
sn*-run (context-∥ₗ r) ((_ , _ , sn f _) ∥ sP) = (_ , _ , f r) ∥ sP
sn*-run (context-∥ᵣ r) (sM ∥ sP) = sM ∥ sn*-run r sP

sn*-↑-∥ : P ↝↝ₚ-[ op , V ] Q → sn* P → sn* Q
sn*-↑-∥ ↑-∥ₗ ((suc _ , _ , sn sM le) ∥ sP) = (_ , _ , sn-strip-↑ (sn sM le)) ∥ sn*-↓ₜ _ _ sP
sn*-↑-∥ (↑-∥ᵣ r) (sM ∥ sP) = sn-↓ _ _ sM ∥ sn*-↑-∥ r sP

sn*-↝ : P ↝↝ₚ Q → sn* P → sn* Q
sn*-↝ (↑-∥ r) sP = sn*-↑-∥ r sP
sn*-↝ (run r) sP = sn*-run r sP


-- INDUCTION MEASURES

-- SUM OF MAXIMUM OUTGOING SIGNALS OVER ALL INDIVIDUAL COMPUTATIONS

∣_∣↑ : sn* P → ℕ
∣ run (n , _) ∣↑ = n
∣ (n , _) ∥ sP ∣↑ = n + ∣ sP ∣↑

-- SUM OF SIZES OF INTERRUPT ANNOTATIONS OVER ALL INDIVIDUAL COMPUTATIONS

∣_∣i : sn* P → ℕ
∣ run {M = M} sM ∣i = ∣ isf-of (type-of M) ∣
∣ _∥_ {M = M} _ sP ∣i = ∣ isf-of (type-of M) ∣ + ∣ sP ∣i

-- SUM OF UPPER BOUNDS ON THE NUMBER OF REDUCTION STEPS OVER ALL INDIVIDUAL COMPUTATIONS

∣_∣↝ : sn* P → ℕ
∣ run (_ , m , _) ∣↝ = m
∣ (_ , m , _) ∥ sP ∣↝ = m + ∣ sP ∣↝


-- REDUCING AN INDIVIDUAL COMPUTATION LEAVES ∣_∣i AND ∣_∣↑ UNCHANGED AND REDUCES ∣_∣↝

run-i-≡ : (r : P ↝↝ₚ-↝ Q) (sP : sn* P) → ∣ sn*-run r sP ∣i ≡ ∣ sP ∣i
run-i-≡ (run r) (run (_ , _ , sn _ _)) = refl
run-i-≡ (context-∥ₗ r) ((_ , _ , sn _ _) ∥ _) = refl
run-i-≡ (context-∥ᵣ r) (_ ∥ sP) = cong (_ +_) (run-i-≡ r sP)

run-↑-≡ : (r : P ↝↝ₚ-↝ Q) (sP : sn* P) → ∣ sn*-run r sP ∣↑ ≡ ∣ sP ∣↑
run-↑-≡ (run r) (run (_ , _ , sn _ _)) = refl
run-↑-≡ (context-∥ₗ r) ((_ , _ , sn _ _) ∥ _) = refl
run-↑-≡ (context-∥ᵣ r) (_ ∥ sP) = cong (_ +_) (run-↑-≡ r sP)

run-↝-< : (r : P ↝↝ₚ-↝ Q) (sP : sn* P) → ∣ sn*-run r sP ∣↝ < ∣ sP ∣↝
run-↝-< (run _) (run (_ , _ , sn _ _)) = ≤-refl
run-↝-< (context-∥ₗ _) ((_ , _ , sn _ _) ∥ _) = ≤-refl
run-↝-< (context-∥ᵣ r) (_ ∥ sP) = +-monoʳ-< _ (run-↝-< r sP)


-- A PREDICATE EXPRESSING THAT AN INTERRUPT HANDLER IS SET UP
-- IN AT LEAST ONE OF THE INDIVIDUAL COMPUTATIONS IN A PARALLEL PROCESS,
-- AND PROOF THAT IT IS DECIDABLE

has : Σₛ → Γ ⊢P⦂ → Set
has op (run M) = [ op ]ₗ ∈ᵢ i-of (type-of M)
has op (M ∥ P) = [ op ]ₗ ∈ᵢ i-of (type-of M) ⊎ has op P

has? : (op : Σₛ) (P : Γ ⊢P⦂) → Dec (has op P)
has? op (run M) = [ op ]ₗ ∈ᵢ? i-of (type-of M)
has? op (M ∥ P) with [ op ]ₗ ∈ᵢ? i-of (type-of M)
... | yes a = yes (inj₁ a)
... | no  a with has? op P
...   | yes a = yes (inj₂ a)
...   | no  b = no (λ {(inj₁ x) → a x; (inj₂ y) → b y})

module _ (op : Σₛ) (V : Γ ⊢V⦂ ```(payload op)) where

  -- ACTING WITH AN INTERRUPT NEVER INCREASES ∣_∣i,
  -- AND DECREASES IT OR LEAVES IT UNCHANGED DEPENDING ON WHETHER A HANDLER FOR THAT INTERRUPT
  -- IS SET UP IN AT LEAST ONE OF THE COMPUTATIONS

  sn*-↓ₜ-i-≤ : (sP : sn* P) → ∣ sn*-↓ₜ op V sP ∣i ≤ ∣ sP ∣i
  sn*-↓ₜ-i-≤ (run {M = M} _) = size-↓ₑ-≤ (isf-of (type-of M))
  sn*-↓ₜ-i-≤ (_∥_ {M = M} _ sP) = +-mono-≤ (size-↓ₑ-≤ (isf-of (type-of M))) (sn*-↓ₜ-i-≤ sP)

  sn*-↓ₜ-i-< : (sP : sn* P) → has op P → ∣ sn*-↓ₜ op V sP ∣i < ∣ sP ∣i
  sn*-↓ₜ-i-< (run {M = M} _) h = size-↓ₑ-< (isf-of (type-of M)) h
  sn*-↓ₜ-i-< (_∥_ {M = M} _ sP) (inj₁ h) = +-mono-<-≤ (size-↓ₑ-< (isf-of (type-of M)) h) (sn*-↓ₜ-i-≤ sP)
  sn*-↓ₜ-i-< (_∥_ {M = M} _ sP) (inj₂ h) = +-mono-≤-< (size-↓ₑ-≤ (isf-of (type-of M))) (sn*-↓ₜ-i-< sP h)

  sn*-↓ₜ-i-≡ : (sP : sn* P) → ¬ has op P → ∣ sn*-↓ₜ op V sP ∣i ≡ ∣ sP ∣i
  sn*-↓ₜ-i-≡ (run {M = M} _) h = size-↓ₑ-≡ (isf-of (type-of M)) h
  sn*-↓ₜ-i-≡ (_∥_ {M = M} _ sP) h with [ op ]ₗ ∈ᵢ? i-of (type-of M)
  ... | yes a = ⊥-elim (h (inj₁ a))
  ... | no  a rewrite sym (size-↓ₑ-≡ (isf-of (type-of M)) a) = cong (_ +_) (sn*-↓ₜ-i-≡ sP (h ∘ inj₂))


  -- IF A HANDLER FOR AN INTERRUPT IS NOT SET UP IN ANY COMPUTATION,
  -- THEN ACTING WITH THAT INTERRUPT LEAVES ∣_∣↑ UNCHANGED

  sn*-↓ₜ-↑-≡ : (sP : sn* P) → ¬ has op P → ∣ sn*-↓ₜ op V sP ∣↑ ≡ ∣ sP ∣↑
  sn*-↓ₜ-↑-≡ (run {M = M} (_ , _ , sn _ _)) h with [ op ]ₗ ∈ᵢ? i-of (type-of M)
  ... | yes a = ⊥-elim (h a)
  ... | no  a = refl
  sn*-↓ₜ-↑-≡ (_∥_ {M = M} _ sP) h with [ op ]ₗ ∈ᵢ? i-of (type-of M)
  ... | yes a = ⊥-elim (h (inj₁ a))
  ... | no  a = cong (_ +_) (sn*-↓ₜ-↑-≡ sP (h ∘ inj₂))


  -- SENDING A SIGNAL EITHER DECREASES ∣_∣i OR LEAVES ∣_∣i UNCHANGED AND DECREASES ∣_∣↑

  ↑-∥-i-< : (r : P ↝↝ₚ-[ op , V ] Q)
            (sP : sn* P) →
            ---------------------------------------------------------
            ∣ sn*-↑-∥ r sP ∣i < ∣ sP ∣i
            ⊎
            ∣ sn*-↑-∥ r sP ∣i ≡ ∣ sP ∣i × ∣ sn*-↑-∥ r sP ∣↑ < ∣ sP ∣↑

  ↑-∥-i-< (↑-∥ₗ {M = M} {P = P}) ((suc _ , _ , sn _ _) ∥ sP) with has? op P
  ... | yes a = inj₁ (+-monoʳ-< _ (sn*-↓ₜ-i-< sP a))
  ... | no  a rewrite sym (sn*-↓ₜ-↑-≡ sP a) = inj₂ (cong (_ +_) (sn*-↓ₜ-i-≡ sP a) , ≤-refl)
  ↑-∥-i-< (↑-∥ᵣ {M = M} r) (sM ∥ sP) with ↑-∥-i-< r sP
  ... | inj₁ le = inj₁ (+-mono-≤-< (size-↓ₑ-≤ (isf-of (type-of M))) le)
  ... | inj₂ (eq , le) with [ op ]ₗ ∈ᵢ? i-of (type-of M)
  ...   | yes a rewrite eq = inj₁ (+-monoˡ-< _ (size-↓ₑ-< (isf-of (type-of M)) a))
  ...   | no  a rewrite eq = inj₂ (cong (_+ _) (size-↓ₑ-≡ (isf-of (type-of M)) a) , +-monoʳ-< _ le)


-- STRONG NORMALISATION PREDICATE FOR PARALLEL COMPUTATIONS

data SNₚ (P : Γ ⊢P⦂) : Set where
  sn : ({Q : Γ ⊢P⦂} → P ↝↝ₚ Q → SNₚ Q) → SNₚ P


-- MAIN INDUCTION COMBINING THE ABOVE RESULTS

strong-normₚ' : (sP : sn* P) →
                Acc _<_ ∣ sP ∣i →
                Acc _<_ ∣ sP ∣↑ →
                Acc _<_ ∣ sP ∣↝ →
                ---------------------------
                {Q : Γ ⊢P⦂} → P ↝↝ₚ Q → SNₚ Q

strong-normₚ' sP _ _ _ (↑-∥ r) with ↑-∥-i-< _ _ r sP
strong-normₚ' sP (acc ai) _ _ (↑-∥ r)  | inj₁ le = sn (strong-normₚ' (sn*-↑-∥ r sP) (ai le) (<-wellFounded _) (<-wellFounded _))
strong-normₚ' sP ai (acc a↑) _ (↑-∥ r) | inj₂ (eq , le) rewrite sym eq = sn (strong-normₚ' (sn*-↑-∥ r sP) ai (a↑ le) (<-wellFounded _))
strong-normₚ' sP ai a↑ (acc a↝) (run r)
  rewrite sym (run-i-≡ r sP) | sym (run-↑-≡ r sP) =
  sn (strong-normₚ' (sn*-run r sP) ai a↑ (a↝ (run-↝-< r sP)))


-- ALL PARALLEL PROCESSES ARE STRONGLY NORMALISING

all-sn* : (P : Γ ⊢P⦂) → sn* P
all-sn* (run M) = run (strong-norm-Σ (strong-norm M))
all-sn* (M ∥ P) = strong-norm-Σ (strong-norm M) ∥ all-sn* P

strong-normₚ : (P : Γ ⊢P⦂) → SNₚ P
strong-normₚ P = sn (strong-normₚ' (all-sn* P) (<-wellFounded _) (<-wellFounded _) (<-wellFounded _))