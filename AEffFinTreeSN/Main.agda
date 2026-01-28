open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; s≤s; _<_; ≤-pred)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoˡ-<; +-monoʳ-<)
open import Data.Nat.Induction renaming (<-wellFounded to <-wf)
open import Data.List using (List) renaming ([_] to [_]ₗ)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import AEffFinTreeSN.AEffSequential
open import AEffFinTreeSN.AEffParallelTree
open import AEffFinTreeSN.FiniteEffectAnnotations
open import AEffFinTreeSN.Simulation
open import AEffFinTreeSN.StronglyNormalising
open import AEffFinTreeSN.ParallelShape

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

module AEffFinTreeSN.Main where

-- FORM M N SAYS THAT M AND N ARE OF FORMS E [ L ] AND E [ ↓ op V L ] RESPECTIVELY

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


-- IF M DOES NOT HAVE A HANDLER FOR op, THEN AN INTERRUPT op PRESERVES THE STRUCTURE OF M

form-↝ : {M : Γ ⊢M⦂ X ! (i , isf)}
         {N : Γ ⊢M⦂ X ! (op ↓ₑ i , fin-↓ₑ op isf)} →
         ¬ [ op ]ₗ ∈ᵢ i →
         Form M N →
         N ↝↝ N' →
         ----------------------------
         Form M N' ⊎ Σ[ M' ∈ _ ] Form M' N' × M ↝↝ M'
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
          ∀ {N'} → N ↝↝ N' → SN↑ N' n
≡-↓-sn' u (sn sM le) (sn sN le') ff r with form-↝ u ff r
... | inj₁ ff = sn (≡-↓-sn' u (sn sM le) (sN r) ff) (≤-trans (form-#↑ ff) le)
... | inj₂ (_ , ff , r') = sn (≡-↓-sn' u (sM r') (sN r) ff) (≤-trans (form-#↑ ff) (sn-#↑ (sM r')))


-- AS A RESULT, ACTING WITH op ON A TERM THAT HAS NO HANDLER FOR op
-- DOES NOT INCREASE THE MAXIMUM NUMBER OF OUTGOING SIGNALS

≡-↓-sn : ¬ [ op ]ₗ ∈ᵢ i-of (type-of M) → SN↑ M n → SN↑ (↓ op V M) n
≡-↓-sn {_} {_} {_ ! _} u s = sn (≡-↓-sn' u s (sn→sn↑ (strong-norm _)) [-]) z≤n


-- HELPER FUNCTIONS

sn-↓ : ΣSN M → ΣSN (↓ op V M)
sn-↓ {M = M} {op} (_ , _ , sM) with [ op ]ₗ ∈ᵢ? i-of (type-of M)
... | yes _ = strong-norm-Σ (strong-norm _)
... | no  a = _ , sn↑-sni↑ (≡-↓-sn a (sni↑→sn↑ sM))

sn-strip-↑ : ΣSN (↑ op V M) → ΣSN M
sn-strip-↑ (_ , _ , sn sM (s≤s le)) = _ , _ , sn-strip-↑' (sn sM (s≤s le))
  where
  sn-strip-↑' : SNi↑ (↑ op V M) (suc n) m → SNi↑ M n m
  sn-strip-↑' (sn sM le) = sn (λ r → sn-strip-↑' (sM (context-↑ r))) (≤-pred le)

sn-strip-↑-< : (sM : ΣSN (↑ op V M)) → proj₁ (sn-strip-↑ sM) < proj₁ sM
sn-strip-↑-< (_ , _ , sn sM (s≤s _)) = ≤-refl


-- FINDING THE PARALLEL SHAPE OF A TERM

par-shape-of : Γ ⊢P⦂ → ParallelShape
par-shape-of (run _) = run
par-shape-of (P ∥ Q) = par-shape-of P ∥ par-shape-of Q
par-shape-of (↑ _ _ P) = ↑ (par-shape-of P)
par-shape-of (↓ _ _ P) = ↓ (par-shape-of P)


-- DATATYPE EXPRESSING THAT EACH INDIVIDUAL COMPUTATION IN A PROCESS
-- IS STRONGLY NORMALISING IN ISOLATION

data sn* : Γ ⊢P⦂ → Set where
  run : ΣSN M → sn* (run M)
  _∥_ : sn* P → sn* Q → sn* (P ∥ Q)
  ↑   : sn* P → sn* (↑ op V P)
  ↓   : sn* P → sn* (↓ op V P)

sn*↝ : P ↝↝ₚ Q → sn* P → sn* Q
sn*↝ (run r) (run (_ , _ , sn f _)) = run (_ , _ , f r)
sn*↝ (↑-∥ₗ _ _ _) (↑ sP ∥ sQ) = ↑ (sP ∥ ↓ sQ)
sn*↝ (↑-∥ᵣ _ _ _) (sP ∥ ↑ sQ) = ↑ (↓ sP ∥ sQ)
sn*↝ (↓-run _ _) (↓ (run s)) = run (sn-↓ s)
sn*↝ (↓-∥ _ _ _) (↓ (sP ∥ sQ)) = ↓ sP ∥ ↓ sQ
sn*↝ (↓-↑ _ _ _) (↓ (↑ sP)) = ↑ (↓ sP)
sn*↝ (↑ _ _) (run sM) = ↑ (run (sn-strip-↑ sM))
sn*↝ (context-∥ₗ r) (sP ∥ sQ) = sn*↝ r sP ∥ sQ
sn*↝ (context-∥ᵣ r) (sP ∥ sQ) = sP ∥ sn*↝ r sQ
sn*↝ (context-↑ r) (↑ sP) = ↑ (sn*↝ r sP)
sn*↝ (context-↓ r) (↓ sP) = ↓ (sn*↝ r sP)


-- INDUCTION MEASURES

-- SUM OF MAXIMUM OUTGOING SIGNALS OVER ALL INDIVIDUAL COMPUTATIONS

∣_∣↑ : sn* P → ℕ
∣ run (n , _) ∣↑ = n
∣ s ∥ t ∣↑ = ∣ s ∣↑ + ∣ t ∣↑
∣ ↑ s ∣↑ = ∣ s ∣↑
∣ ↓ s ∣↑ = ∣ s ∣↑

-- SUM OF SIZES OF INTERRUPT ANNOTATIONS OVER ALL INDIVIDUAL COMPUTATIONS

∣_∣i : sn* P → ℕ
∣ run {M = M} _ ∣i = ∣ isf-of (type-of M) ∣
∣ s ∥ t ∣i = ∣ s ∣i + ∣ t ∣i
∣ ↑ s ∣i = ∣ s ∣i
∣ ↓ s ∣i = ∣ s ∣i

-- SUM OF UPPER BOUNDS ON THE NUMBER OF REDUCTION STEPS OVER ALL INDIVIDUAL COMPUTATIONS

∣_∣↝ : sn* P → ℕ
∣ run (_ , m , _) ∣↝ = m
∣ s ∥ t ∣↝ = ∣ s ∣↝ + ∣ t ∣↝
∣ ↑ s ∣↝ = ∣ s ∣↝
∣ ↓ s ∣↝ = ∣ s ∣↝


-- TYPES OF REDUCTIONS

data ↝-type : Set where
  ↑-run ↓-run ↝-run ↝-shape : ↝-type

↝-type-of : P ↝↝ₚ Q → ↝-type
↝-type-of (run _) = ↝-run
↝-type-of (↑-∥ₗ _ _ _) = ↝-shape
↝-type-of (↑-∥ᵣ _ _ _) = ↝-shape
↝-type-of (↓-run _ _) = ↓-run
↝-type-of (↓-∥ _ _ _) = ↝-shape
↝-type-of (↓-↑ _ _ _) = ↝-shape
↝-type-of (↑ _ _) = ↑-run
↝-type-of (context-∥ₗ r) = ↝-type-of r
↝-type-of (context-∥ᵣ r) = ↝-type-of r
↝-type-of (context-↑ r) = ↝-type-of r
↝-type-of (context-↓ r) = ↝-type-of r


-- PROOFS OF WHICH INDUCTION MEASURES GET DECREASED/LEFT UNCHANGED BY WHICH REDUCTION TYPES

-- ↑-RUN REDUCTIONS LEAVE ∣_∣i UNCHANGED AND DECREASE ∣_∣↑

↑-run-≡i : (r : P ↝↝ₚ Q) (sP : sn* P) →
           ↝-type-of r ≡ ↑-run →
           ------------------------
           ∣ sn*↝ r sP ∣i ≡ ∣ sP ∣i
↑-run-≡i (↑ _ _) (run _) _ = refl
↑-run-≡i (context-∥ₗ r) (sP ∥ _) eq = cong (_+ _) (↑-run-≡i r sP eq)
↑-run-≡i (context-∥ᵣ r) (_ ∥ sQ) eq = cong (_ +_) (↑-run-≡i r sQ eq)
↑-run-≡i (context-↑ r) (↑ sP) eq = ↑-run-≡i r sP eq
↑-run-≡i (context-↓ r) (↓ sP) eq = ↑-run-≡i r sP eq

↑-run-<↑ : (r : P ↝↝ₚ Q) (sP : sn* P) →
           ↝-type-of r ≡ ↑-run →
           ------------------------
           ∣ sn*↝ r sP ∣↑ < ∣ sP ∣↑
↑-run-<↑ (↑ _ _) (run sM) _ = sn-strip-↑-< sM
↑-run-<↑ (context-∥ₗ r) (sP ∥ _) eq = +-monoˡ-< _ (↑-run-<↑ r sP eq)
↑-run-<↑ (context-∥ᵣ r) (_ ∥ sQ) eq = +-monoʳ-< _ (↑-run-<↑ r sQ eq)
↑-run-<↑ (context-↑ r) (↑ sP) eq = ↑-run-<↑ r sP eq
↑-run-<↑ (context-↓ r) (↓ sP) eq = ↑-run-<↑ r sP eq


-- ↓-RUN REDUCTIONS EITHER DECREASE ∣_∣i OR LEAVE BOTH ∣_∣i AND ∣_∣↑ UNCHANGED

↓-run-< : (r : P ↝↝ₚ Q) (sP : sn* P) →
          ↝-type-of r ≡ ↓-run →
          -------------------------
          ∣ sn*↝ r sP ∣i < ∣ sP ∣i
          ⊎
          ∣ sn*↝ r sP ∣i ≡ ∣ sP ∣i × ∣ sn*↝ r sP ∣↑ ≡ ∣ sP ∣↑
↓-run-< (↓-run {op = op} _ M) (↓ (run sM)) _ with [ op ]ₗ ∈ᵢ? i-of (type-of M)
... | yes a = inj₁ (size-↓ₑ-< (isf-of (type-of M)) a)
... | no  a = inj₂ (size-↓ₑ-≡ (isf-of (type-of M)) a , refl)
↓-run-< (context-∥ₗ r) (sP ∥ _) eq with ↓-run-< r sP eq
... | inj₁ x = inj₁ (+-monoˡ-< _ x)
... | inj₂ (x , y) rewrite x | y = inj₂ (refl , refl)
↓-run-< (context-∥ᵣ r) (_ ∥ sQ) eq with ↓-run-< r sQ eq
... | inj₁ x = inj₁ (+-monoʳ-< _ x)
... | inj₂ (x , y) rewrite x | y = inj₂ (refl , refl)
↓-run-< (context-↑ r) (↑ sP) eq = ↓-run-< r sP eq
↓-run-< (context-↓ r) (↓ sP) eq = ↓-run-< r sP eq

-- ↓-RUN REDUCTIONS DECREASE ∣_∣p

↓-run-⇝ : (r : P ↝↝ₚ Q) →
          ↝-type-of r ≡ ↓-run →
          -------------------------------
          par-shape-of P ⇝ par-shape-of Q
↓-run-⇝ (↓-run _ _) _ = ↓-run
↓-run-⇝ (context-∥ₗ r) eq = context-∥ₗ (↓-run-⇝ r eq)
↓-run-⇝ (context-∥ᵣ r) eq = context-∥ᵣ (↓-run-⇝ r eq)
↓-run-⇝ (context-↑ r) eq = context-↑ (↓-run-⇝ r eq)
↓-run-⇝ (context-↓ r) eq = context-↓ (↓-run-⇝ r eq)

↓-run-<p : (r : P ↝↝ₚ Q) →
           ↝-type-of r ≡ ↓-run →
           ------------------------
           ∣ par-shape-of Q ∣p <ₗₑₓ ∣ par-shape-of P ∣p
↓-run-<p r eq = maxs-< (↓-run-⇝ r eq)


-- ↝-SHAPE REDUCTIONS LEAVE ∣_∣i AND ∣_∣↑ UNCHANGED AND DECREASE ∣_∣p

↝-shape-≡i : (r : P ↝↝ₚ Q) (sP : sn* P) →
             ↝-type-of r ≡ ↝-shape →
             ------------------------
             ∣ sn*↝ r sP ∣i ≡ ∣ sP ∣i
↝-shape-≡i (↑-∥ₗ _ _ _) (↑ _ ∥ _) _ = refl
↝-shape-≡i (↑-∥ᵣ _ _ _) (_ ∥ ↑ _) _ = refl
↝-shape-≡i (↓-∥ _ _ _) (↓ (_ ∥ _)) _ = refl
↝-shape-≡i (↓-↑ _ _ _) (↓ (↑ _)) _ = refl
↝-shape-≡i (context-∥ₗ r) (sP ∥ _) eq = cong (_+ _) (↝-shape-≡i r sP eq)
↝-shape-≡i (context-∥ᵣ r) (_ ∥ sQ) eq = cong (_ +_) (↝-shape-≡i r sQ eq)
↝-shape-≡i (context-↑ r) (↑ sP) eq = ↝-shape-≡i r sP eq
↝-shape-≡i (context-↓ r) (↓ sP) eq = ↝-shape-≡i r sP eq

↝-shape-≡↑ : (r : P ↝↝ₚ Q) (sP : sn* P) →
             ↝-type-of r ≡ ↝-shape →
             ------------------------
             ∣ sn*↝ r sP ∣↑ ≡ ∣ sP ∣↑
↝-shape-≡↑ (↑-∥ₗ _ _ _) (↑ _ ∥ _) _ = refl
↝-shape-≡↑ (↑-∥ᵣ _ _ _) (_ ∥ ↑ _) _ = refl
↝-shape-≡↑ (↓-∥ _ _ _) (↓ (_ ∥ _)) _ = refl
↝-shape-≡↑ (↓-↑ _ _ _) (↓ (↑ _)) _ = refl
↝-shape-≡↑ (context-∥ₗ r) (sP ∥ _) eq = cong (_+ _) (↝-shape-≡↑ r sP eq)
↝-shape-≡↑ (context-∥ᵣ r) (_ ∥ sQ) eq = cong (_ +_) (↝-shape-≡↑ r sQ eq)
↝-shape-≡↑ (context-↑ r) (↑ sP) eq = ↝-shape-≡↑ r sP eq
↝-shape-≡↑ (context-↓ r) (↓ sP) eq = ↝-shape-≡↑ r sP eq

↝-shape-⇝ : (r : P ↝↝ₚ Q) →
            ↝-type-of r ≡ ↝-shape →
            ------------------------
            par-shape-of P ⇝ par-shape-of Q
↝-shape-⇝ (↑-∥ₗ _ _ _) _ = ↑-∥ₗ
↝-shape-⇝ (↑-∥ᵣ _ _ _) _ = ↑-∥ᵣ
↝-shape-⇝ (↓-∥ _ _ _) _ = ↓-∥
↝-shape-⇝ (↓-↑ _ _ _) _ = ↓-↑
↝-shape-⇝ (context-∥ₗ r) eq = context-∥ₗ (↝-shape-⇝ r eq)
↝-shape-⇝ (context-∥ᵣ r) eq = context-∥ᵣ (↝-shape-⇝ r eq)
↝-shape-⇝ (context-↑ r) eq = context-↑ (↝-shape-⇝ r eq)
↝-shape-⇝ (context-↓ r) eq = context-↓ (↝-shape-⇝ r eq)

↝-shape-<p : (r : P ↝↝ₚ Q) →
             ↝-type-of r ≡ ↝-shape →
             ------------------------
             ∣ par-shape-of Q ∣p <ₗₑₓ ∣ par-shape-of P ∣p
↝-shape-<p r eq = maxs-< (↝-shape-⇝ r eq)


-- ↝-RUN REDUCTIONS LEAVE ∣_∣i, ∣_∣↑ AND ∣_∣p UNCHANGED AND DECREASE ∣_∣↝

↝-run-≡i : (r : P ↝↝ₚ Q) (sP : sn* P) →
           ↝-type-of r ≡ ↝-run →
           ------------------------
           ∣ sn*↝ r sP ∣i ≡ ∣ sP ∣i
↝-run-≡i (run _) (run (_ , _ , sn _ _)) _ = refl
↝-run-≡i (context-∥ₗ r) (sP ∥ _) eq = cong (_+ _) (↝-run-≡i r sP eq)
↝-run-≡i (context-∥ᵣ r) (_ ∥ sQ) eq = cong (_ +_) (↝-run-≡i r sQ eq)
↝-run-≡i (context-↑ r) (↑ sP) eq = ↝-run-≡i r sP eq
↝-run-≡i (context-↓ r) (↓ sP) eq = ↝-run-≡i r sP eq

↝-run-≡↑ : (r : P ↝↝ₚ Q) (sP : sn* P) →
           ↝-type-of r ≡ ↝-run →
           ------------------------
           ∣ sn*↝ r sP ∣↑ ≡ ∣ sP ∣↑
↝-run-≡↑ (run _) (run (_ , _ , sn _ _)) _ = refl
↝-run-≡↑ (context-∥ₗ r) (sP ∥ _) eq = cong (_+ _) (↝-run-≡↑ r sP eq)
↝-run-≡↑ (context-∥ᵣ r) (_ ∥ sQ) eq = cong (_ +_) (↝-run-≡↑ r sQ eq)
↝-run-≡↑ (context-↑ r) (↑ sP) eq = ↝-run-≡↑ r sP eq
↝-run-≡↑ (context-↓ r) (↓ sP) eq = ↝-run-≡↑ r sP eq

↝-run-≡s : (r : P ↝↝ₚ Q) →
           ↝-type-of r ≡ ↝-run →
           -------------------------------
           par-shape-of Q ≡ par-shape-of P
↝-run-≡s (run _) _ = refl
↝-run-≡s (context-∥ₗ r) eq = cong (_∥ _) (↝-run-≡s r eq)
↝-run-≡s (context-∥ᵣ r) eq = cong (_ ∥_) (↝-run-≡s r eq)
↝-run-≡s (context-↑ r) eq = cong ↑ (↝-run-≡s r eq)
↝-run-≡s (context-↓ r) eq = (cong ↓) (↝-run-≡s r eq)

↝-run-≡p : (r : P ↝↝ₚ Q) →
           ↝-type-of r ≡ ↝-run →
           -----------------------------------------
           ∣ par-shape-of Q ∣p ≡ ∣ par-shape-of P ∣p
↝-run-≡p r eq = cong ∣_∣p (↝-run-≡s r eq)

↝-run-<↝ : (r : P ↝↝ₚ Q) (sP : sn* P) →
           ↝-type-of r ≡ ↝-run →
           ------------------------
           ∣ sn*↝ r sP ∣↝ < ∣ sP ∣↝
↝-run-<↝ (run _) (run (_ , _ , sn _ _)) _ = ≤-refl
↝-run-<↝ (context-∥ₗ r) (sP ∥ _) eq = +-monoˡ-< _ (↝-run-<↝ r sP eq)
↝-run-<↝ (context-∥ᵣ r) (_ ∥ sQ) eq = +-monoʳ-< _ (↝-run-<↝ r sQ eq)
↝-run-<↝ (context-↑ r) (↑ sP) eq = ↝-run-<↝ r sP eq
↝-run-<↝ (context-↓ r) (↓ sP) eq = ↝-run-<↝ r sP eq


-- STRONG NORMALISATION PREDICATE FOR PARALLEL COMPUTATIONS

data SNₚ (P : Γ ⊢P⦂) : Set where
  sn : ({Q : Γ ⊢P⦂} → P ↝↝ₚ Q → SNₚ Q) → SNₚ P


-- MAIN INDUCTION COMBINING THE ABOVE RESULTS

strong-normₚ' : (sP : sn* P) →
                Acc _<_ (∣ sP ∣i) →
                Acc _<_ (∣ sP ∣↑) →
                Acc _<ₗₑₓ_ (∣ par-shape-of P ∣p) →
                Acc _<_ (∣ sP ∣↝) →
                ---------------------------
                {Q : Γ ⊢P⦂} → P ↝↝ₚ Q → SNₚ Q
strong-normₚ' sP ai a↑ ap a↝ r with ↝-type-of r in eq
strong-normₚ' sP ai (acc a↑) _ _ r | ↑-run
  rewrite
  sym (↑-run-≡i r sP eq) =
  sn (strong-normₚ' (sn*↝ r sP) ai (a↑ (↑-run-<↑ r sP eq)) (<ₗₑₓ-wf _) (<-wf _))
strong-normₚ' sP ai a↑ (acc ap) _ r | ↝-shape
  rewrite
  sym (↝-shape-≡i r sP eq) |
  sym (↝-shape-≡↑ r sP eq) =
  sn (strong-normₚ' (sn*↝ r sP) ai a↑ (ap (↝-shape-<p r eq)) (<-wf _))
strong-normₚ' sP ai a↑ ap (acc a↝) r | ↝-run
  rewrite
  sym (↝-run-≡i r sP eq) |
  sym (↝-run-≡↑ r sP eq) |
  sym (↝-run-≡p r eq) =
  sn (strong-normₚ' (sn*↝ r sP) ai a↑ ap (a↝ (↝-run-<↝ r sP eq)))
strong-normₚ' sP ai a↑ (acc ap) a↝ r | ↓-run with ↓-run-< r sP eq
... | inj₁ x
  with acc ai ← ai =
  sn (strong-normₚ' (sn*↝ r sP) (ai x) (<-wf _) (<ₗₑₓ-wf _) (<-wf _))
... | inj₂ (x , y)
  rewrite sym x | sym y =
  sn (strong-normₚ' (sn*↝ r sP) ai a↑ (ap (↓-run-<p r eq)) (<-wf _))

all-sn* : (P : Γ ⊢P⦂) → sn* P
all-sn* (run M) = run (strong-norm-Σ (strong-norm M))
all-sn* (P ∥ Q) = all-sn* P ∥ all-sn* Q
all-sn* (↑ _ _ P) = ↑ (all-sn* P)
all-sn* (↓ _ _ P) = ↓ (all-sn* P)

strong-normₚ : (P : Γ ⊢P⦂) → SNₚ P
strong-normₚ P = sn (strong-normₚ' (all-sn* P) (<-wf _) (<-wf _) (<ₗₑₓ-wf _) (<-wf _))