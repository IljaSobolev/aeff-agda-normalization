open import AEffFinTreeSN.FiniteEffectAnnotations
open import AEffFinTreeSN.AEffSequential
open import AEffBaseSN.StronglyNormalising using (_∈ₗ_; Hd; Tl; map-∈ₗ; ⊔-∈ₗ-≤; ++-∈ₗ)

open import AEff.EffectAnnotations using (decₛ)

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _<_; _⊔_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⇒m≤o⊔n)
open import Data.List using (List) renaming ([] to []ₗ; _∷_ to _∷ₗ_; _++_ to _++ₗ_; [_] to [_]ₗ; map to mapₗ; foldr to foldrₗ)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Function using (_∘_)

module AEffFinTreeSN.StronglyNormalising where

variable
  n m k : ℕ

-- EACH TERM CAN ONLY HAVE FINITELY MANY REDUCTS

data Reduct (M : Γ ⊢M⦂ C) : Set where
  r↝ : M ↝↝ N → Reduct M

reducts-base : (M : Γ ⊢M⦂ X ! (i , isf)) → List (Reduct M)

reducts-base (ƛ _ · _) =
  [ r↝ (apply _ _) ]ₗ
reducts-base (await ⟨ _ ⟩ until _) =
  [ r↝ (await-promise _ _) ]ₗ
reducts-base (let= return _ `in _) =
  [ r↝ (let-return _ _) ]ₗ
reducts-base (↓ _ _ (return _)) =
  [ r↝ (↓-return _ _) ]ₗ
reducts-base (promise _ ∣ _ , _ ↦ _ `in ↑ _ _ _) =
  [ r↝ (promise-↑ _ _ _ _ _) ]ₗ
reducts-base (let= ↑ _ _ _ `in _) =
  [ r↝ (let-↑ _ _ _) ]ₗ
reducts-base (let= promise _ ∣ _ , _ ↦ _ `in _ `in _) =
  [ r↝ (let-promise _ _ _ _ _) ]ₗ
reducts-base (let= await _ until _ `in _) =
  [ r↝ (let-await _ _ _) ]ₗ
reducts-base (↓ {C = _ ! _} _ _ (↑ _ _ _)) =
  [ r↝ (↓-↑ _ _ _) ]ₗ
reducts-base (↓ {C = _ ! _} op _ (promise op' ∣ _ , _ ↦ _ `in _)) with decₛ op op'
... | yes refl =
  [ r↝ (↓-promise-op _ _ _ _ _) ]ₗ
... | no     a =
  [ r↝ (↓-promise-op' _ _ _ a _ _) ]ₗ
reducts-base (↓ {C = _ ! _} _ _ (await _ until _)) =
  [ r↝ (↓-await _ _ _) ]ₗ
reducts-base (coerce _ (return _)) =
  [ r↝ (coerce-return _) ]ₗ
reducts-base (coerce _ (↑ _ _ _)) =
  [ r↝ (coerce-↑ _ _) ]ₗ
reducts-base (coerce _ (promise _ ∣ _ , _ ↦ _ `in _)) =
  [ r↝ (coerce-promise _ _ _ _ _) ]ₗ
reducts-base (coerce _ (await _ until _)) =
  [ r↝ (coerce-await _ _) ]ₗ
reducts-base _ =
  []ₗ

ctx-↑ : Reduct M → Reduct (↑ op V M)
ctx-↑ (r↝ r) = r↝ (context-↑ r)

ctx-↓ : Reduct M → Reduct (↓ op V M)
ctx-↓ (r↝ r) = r↝ (context-↓ r)

ctx-promise : Reduct N → Reduct (promise op ∣ x , y ↦ M `in N)
ctx-promise (r↝ r) = r↝ (context-promise r)

ctx-let : Reduct M → Reduct (let= M `in N)
ctx-let (r↝ r) = r↝ (context-let r)

ctx-coerce : Reduct M → Reduct (coerce {isf' = isf'} x M)
ctx-coerce (r↝ r) = r↝ (context-coerce r)

reducts-ctx : (M : Γ ⊢M⦂ X ! (i , isf)) → List (Reduct M)

reducts-ctx (return _) = []ₗ
reducts-ctx (_ · _) = []ₗ
reducts-ctx (let= M `in _) = mapₗ ctx-let (reducts-base M ++ₗ reducts-ctx M)
reducts-ctx (↑ _ _ M) = mapₗ ctx-↑ (reducts-base M ++ₗ reducts-ctx M)
reducts-ctx (↓ {C = _ ! _} _ _ M) = mapₗ ctx-↓ (reducts-base M ++ₗ reducts-ctx M)
reducts-ctx (promise _ ∣ _ , _ ↦ _ `in N) = mapₗ ctx-promise (reducts-base N ++ₗ reducts-ctx N)
reducts-ctx (coerce _ M) = mapₗ ctx-coerce (reducts-base M ++ₗ reducts-ctx M)
reducts-ctx (await _ until _) = []ₗ

reducts-complete' : (R : Reduct M) → R ∈ₗ reducts-base M ⊎ R ∈ₗ reducts-ctx M

reducts-complete' (r↝ (apply M V)) = inj₁ Hd
reducts-complete' (r↝ (let-return V N)) = inj₁ Hd
reducts-complete' (r↝ (let-↑ N V M)) = inj₁ Hd
reducts-complete' (r↝ (↓-↑ V' V M)) = inj₁ Hd
reducts-complete' (r↝ (promise-↑ p q V M N)) = inj₁ Hd
reducts-complete' (r↝ (↓-return V W)) = inj₁ Hd
reducts-complete' (r↝ (let-promise p q L M N)) = inj₁ Hd
reducts-complete' (r↝ (↓-promise-op {op = op} p q V M N)) with decₛ op op
... | yes refl = inj₁ Hd
... | no     p = ⊥-elim (p refl)
reducts-complete' (r↝ (↓-promise-op' {op = op} {op' = op'} V p q r M N)) with decₛ op op'
... | yes refl = ⊥-elim (r refl)
... | no     p = inj₁ Hd
reducts-complete' (r↝ (let-await N V M)) = inj₁ Hd
reducts-complete' (r↝ (↓-await {C = _ ! _} W V M)) = inj₁ Hd
reducts-complete' (r↝ (await-promise V M)) = inj₁ Hd
reducts-complete' (r↝ (coerce-return V)) = inj₁ Hd
reducts-complete' (r↝ (coerce-↑ V M)) = inj₁ Hd
reducts-complete' (r↝ (coerce-promise x p q M N)) = inj₁ Hd
reducts-complete' (r↝ (coerce-await V M)) = inj₁ Hd
reducts-complete' (r↝ (context-let r)) = inj₂ (map-∈ₗ (++-∈ₗ (reducts-complete' (r↝ r))))
reducts-complete' (r↝ (context-↑ r)) = inj₂ (map-∈ₗ (++-∈ₗ (reducts-complete' (r↝ r))))
reducts-complete' (r↝ (context-↓ {_} {_ ! _} r)) = inj₂ (map-∈ₗ (++-∈ₗ (reducts-complete' (r↝ r))))
reducts-complete' (r↝ (context-promise r)) = inj₂ (map-∈ₗ (++-∈ₗ (reducts-complete' (r↝ r))))
reducts-complete' (r↝ (context-coerce r)) = inj₂ (map-∈ₗ (++-∈ₗ (reducts-complete' (r↝ r))))

reducts : (M : Γ ⊢M⦂ X ! (i , isf)) → List (Reduct M)
reducts M = reducts-base M ++ₗ reducts-ctx M

reducts-complete : (R : Reduct M) → R ∈ₗ reducts M
reducts-complete R = ++-∈ₗ (reducts-complete' R)


-- STRONG NORMALISATION PREDICATE

data SN (M : Γ ⊢M⦂ C) : Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝↝ N → SN N) → SN M


-- STRONG NORMALISATION PREDICATE INDEXED BY MAXIMUM REDUCTION LENGTH

data SNi (M : Γ ⊢M⦂ C) : ℕ → Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝↝ N → SNi N n) → SNi M (suc n)

max : SN M → ℕ
max {_} {_ ! _} (sn sM) = suc (foldrₗ _⊔_ 0 (mapₗ (λ {(r↝ r) → max (sM r)}) (reducts _)))

sni-≤ : n ≤ m → SNi M n → SNi M m
sni-≤ (s≤s p) (sn sM) = sn (sni-≤ p ∘ sM)

sn→sni : (s : SN M) → SNi M (max s)
sn→sni {_} {_ ! _} (sn sM) = sn (λ r → sni-≤ (⊔-∈ₗ-≤ (map-∈ₗ (reducts-complete (r↝ r)))) (sn→sni (sM r)))


-- STRONG NORMALISATION PREDICATE INDEXED BY MAXIMUM NUMBER OF OUTGOING SIGNALS

#↑ : Γ ⊢M⦂ C → ℕ
#↑ (↑ _ _ M) = suc (#↑ M)
#↑ _ = 0

data SN↑ (M : Γ ⊢M⦂ C) (n : ℕ) : Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝↝ N → SN↑ N n) → #↑ M ≤ n → SN↑ M n

max↑ : SN M → ℕ
max↑ {_} {_ ! _} {M = M} (sn sM) = #↑ M ⊔ foldrₗ _⊔_ 0 (mapₗ (λ {(r↝ r) → max↑ (sM r)}) (reducts _))

sn↑-≤ : n ≤ m → SN↑ M n → SN↑ M m
sn↑-≤ p (sn sM q) = sn (sn↑-≤ p ∘ sM) (≤-trans q p)

sn→sn↑ : (s : SN M) → SN↑ M (max↑ s)
sn→sn↑ {_} {_ ! _} (sn sM) = sn (λ r → sn↑-≤ (m≤n⇒m≤o⊔n _ (⊔-∈ₗ-≤ (map-∈ₗ (reducts-complete (r↝ r))))) (sn→sn↑ (sM r))) (m≤m⊔n _ _)


-- STRONG NORMALISATION PREDICATE INDEXED BY BOTH MAXIMUM REDUCTION LENGTH AND MAXIMUM NUMBER OF OUTGOING SIGNALS

data SNi↑ (M : Γ ⊢M⦂ C) (n : ℕ) : ℕ → Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝↝ N → SNi↑ N n m) → #↑ M ≤ n → SNi↑ M n (suc m)

ΣSN : Γ ⊢M⦂ C → Set
ΣSN M = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] SNi↑ M n m

sni↑→sn↑ : SNi↑ M n m → SN↑ M n
sni↑→sn↑ (sn sM le) = sn (λ r → sni↑→sn↑ (sM r)) le

sn↑→sn : SN↑ M n → SN M
sn↑→sn (sn sM _) = sn (λ r → sn↑→sn (sM r))

sn↑×sni→sni↑ : SN↑ M n → SNi M m → SNi↑ M n m
sn↑×sni→sni↑ (sn sM le) (sn sM') = sn (λ r → sn↑×sni→sni↑ (sM r) (sM' r)) le

sn↑-sni↑ : SN↑ M n → Σ[ m ∈ ℕ ] SNi↑ M n m
sn↑-sni↑ s = _ , sn↑×sni→sni↑ s (sn→sni (sn↑→sn s))

strong-norm-Σ : SN M → ΣSN M
strong-norm-Σ s = _ , _ , sn↑×sni→sni↑ (sn→sn↑ s) (sn→sni s)

sn-#↑ : SN↑ M n → #↑ M ≤ n
sn-#↑ (sn _ le) = le