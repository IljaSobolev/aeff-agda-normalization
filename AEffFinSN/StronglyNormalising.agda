open import AEffFinSN.FiniteEffectAnnotations
open import AEffFinSN.AEffFin
open import AEffStarSN.StronglyNormalising using (_∈ₗ_; Hd; Tl; map-∈ₗ; ⊔-∈ₗ-≤)

open import EffectAnnotations using (decₛ)

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _<_; _⊔_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⇒m≤o⊔n)
open import Data.List using (List) renaming ([] to []ₗ; _∷_ to _∷ₗ_; [_] to [_]ₗ; map to mapₗ; foldr to foldrₗ)
open import Data.Product using (Σ-syntax; _,_)

open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Function using (_∘_)

module AEffFinSN.StronglyNormalising where

variable
  n m k : ℕ

data Reduct (M : Γ ⊢M⦂ C) : Set where
  r↝ : M ↝ N → Reduct M

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

reducts : (M : Γ ⊢M⦂ X ! (i , isf)) → List (Reduct M)
reducts (ƛ _ · _) =
  r↝ (apply _ _) ∷ₗ []ₗ
reducts (await ⟨ _ ⟩ until _) =
  r↝ (await-promise _ _) ∷ₗ []ₗ
reducts (let= return _ `in _) =
  r↝ (let-return _ _) ∷ₗ []ₗ
reducts (↓ _ _ (return _)) =
  r↝ (↓-return _ _) ∷ₗ []ₗ
reducts (promise _ ∣ _ , _ ↦ _ `in ↑ _ _ _) =
  r↝ (promise-↑ _ _ _ _ _) ∷ₗ mapₗ ctx-promise (reducts _)
reducts (let= ↑ _ _ _ `in _) =
  r↝ (let-↑ _ _ _) ∷ₗ mapₗ ctx-let (reducts _)
reducts (let= promise _ ∣ _ , _ ↦ _ `in _ `in _) =
  r↝ (let-promise _ _ _ _ _) ∷ₗ mapₗ ctx-let (reducts _)
reducts (let= await _ until _ `in _) =
  r↝ (let-await _ _ _) ∷ₗ mapₗ ctx-let (reducts _)
reducts (↓ {C = _ ! _} _ _ (↑ _ _ _)) =
  r↝ (↓-↑ _ _ _) ∷ₗ mapₗ ctx-↓ (reducts _)
reducts (↓ {C = _ ! _} op _ (promise op' ∣ _ , _ ↦ _ `in _)) with decₛ op op' | reducts _
... | yes refl | rec =
  r↝ (↓-promise-op _ _ _ _ _) ∷ₗ mapₗ ctx-↓ rec
... | no     a | rec =
  r↝ (↓-promise-op' _ _ _ a _ _) ∷ₗ mapₗ ctx-↓ rec
reducts (↓ {C = _ ! _} _ _ (await _ until _)) =
  r↝ (↓-await _ _ _) ∷ₗ mapₗ ctx-↓ (reducts _)
reducts (coerce _ (return _)) =
  r↝ (coerce-return _) ∷ₗ []ₗ
reducts (coerce _ (↑ _ _ _)) =
  r↝ (coerce-↑ _ _) ∷ₗ mapₗ ctx-coerce (reducts _)
reducts (coerce _ (promise _ ∣ _ , _ ↦ _ `in _)) =
  r↝ (coerce-promise _ _ _ _ _) ∷ₗ mapₗ ctx-coerce (reducts _)
reducts (promise _ ∣ _ , _ ↦ _ `in _) =
  mapₗ ctx-promise (reducts _)
reducts (let= _ `in _) =
  mapₗ ctx-let (reducts _)
reducts (↓ {C = _ ! _} _ _ _) =
  mapₗ ctx-↓ (reducts _)
reducts (↑ _ _ _) =
  mapₗ ctx-↑ (reducts _)
reducts (coerce _ _) =
  mapₗ ctx-coerce (reducts _)
reducts _ =
  []ₗ

reducts-complete : {M : Γ ⊢M⦂ X ! (i , isf)} (R : Reduct M) → R ∈ₗ reducts M
reducts-complete (r↝ (apply _ _)) = Hd
reducts-complete (r↝ (let-return _ _)) = Hd
reducts-complete (r↝ (let-↑ _ _ _)) = Hd
reducts-complete (r↝ (↓-↑ _ _ _)) = Hd
reducts-complete (r↝ (let-promise _ _ _ _ _)) = Hd
reducts-complete (r↝ (↓-promise-op {op = op} _ _ _ _ _)) with decₛ op op
... | yes refl = Hd
... | no     a = ⊥-elim (a refl)
reducts-complete (r↝ (let-await _ _ _)) = Hd
reducts-complete (r↝ (↓-await {C = _ ! _} _ _ _)) = Hd
reducts-complete (r↝ (promise-↑ _ _ _ _ _)) = Hd
reducts-complete (r↝ (↓-return _ _)) = Hd
reducts-complete (r↝ (await-promise _ _)) = Hd
reducts-complete (r↝ (context-↑ r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = ↑ _ _ _} r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-promise {N = _ · _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = promise _ ∣ _ , _ ↦ _ `in _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = await _ until _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = let= _ `in _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = ↓ _ _ _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = coerce _ _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-let {M = _ · _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-let {M = ↑ _ _ _} r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-let {M = promise _ ∣ _ , _ ↦ _ `in _} r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-let {M = await _ until _} r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-let {M = let= _ `in _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-let {M = ↓ _ _ _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-let {M = coerce _ _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-↓ {_} {_ ! _} {M = _ · _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-↓ {_} {_ ! _} {M = ↑ _ _ _} r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-↓ {_} {_ ! _} {M = promise op' ∣ _ , _ ↦ _ `in _} {op = op} r)) with decₛ op op' | reducts-complete (r↝ r)
... | yes refl | rec = Tl (map-∈ₗ rec)
... | no     a | rec = Tl (map-∈ₗ rec)
reducts-complete (r↝ (context-↓ {_} {_ ! _} {M = await _ until _} r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-↓ {_} {_ ! _} {M = let= _ `in _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-↓ {_} {_ ! _} {M = ↓ _ _ _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-↓ {_} {_ ! _} {M = coerce _ _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (↓-promise-op' {op = op} {op' = op'} V p q r M N)) with decₛ op op'
... | yes refl = ⊥-elim (r refl)
... | no     a = Hd
reducts-complete (r↝ (context-coerce {M = _ · _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-coerce {M = let= _ `in _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-coerce {M = ↑ _ _ _} r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-coerce {M = ↓ _ _ _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-coerce {M = promise _ ∣ _ , _ ↦ _ `in _} r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-coerce {M = await _ until _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-coerce {M = coerce _ _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (coerce-return _)) = Hd
reducts-complete (r↝ (coerce-↑ _ _)) = Hd
reducts-complete (r↝ (coerce-promise _ _ _ _ _)) = Hd

data SN (M : Γ ⊢M⦂ C) : Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝ N → SN N) → SN M

data SNi (M : Γ ⊢M⦂ C) : ℕ → Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝ N → SNi N n) → SNi M (suc n)

max : SN M → ℕ
max {_} {_ ! _} (sn sM) = suc (foldrₗ _⊔_ 0 (mapₗ (λ {(r↝ r) → max (sM r)}) (reducts _)))

sni-≤ : n ≤ m → SNi M n → SNi M m
sni-≤ (s≤s p) (sn sM) = sn (sni-≤ p ∘ sM)

sn→sni : (s : SN M) → SNi M (max s)
sn→sni {_} {_ ! _} (sn sM) = sn (λ r → sni-≤ (⊔-∈ₗ-≤ (map-∈ₗ (reducts-complete (r↝ r)))) (sn→sni (sM r)))

#↑ : Γ ⊢M⦂ C → ℕ
#↑ (↑ _ _ M) = suc (#↑ M)
#↑ _ = 0

data SN↑ (M : Γ ⊢M⦂ C) (n : ℕ) : Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝ N → SN↑ N n) → #↑ M ≤ n → SN↑ M n

max↑ : SN M → ℕ
max↑ {_} {_ ! _} {M = M} (sn sM) = #↑ M ⊔ foldrₗ _⊔_ 0 (mapₗ (λ {(r↝ r) → max↑ (sM r)}) (reducts _))

sn↑-≤ : n ≤ m → SN↑ M n → SN↑ M m
sn↑-≤ p (sn sM q) = sn (sn↑-≤ p ∘ sM) (≤-trans q p)

sn→sn↑ : (s : SN M) → SN↑ M (max↑ s)
sn→sn↑ {_} {_ ! _} (sn sM) = sn (λ r → sn↑-≤ (m≤n⇒m≤o⊔n _ (⊔-∈ₗ-≤ (map-∈ₗ (reducts-complete (r↝ r))))) (sn→sn↑ (sM r))) (m≤m⊔n _ _)

data SNi↑ (M : Γ ⊢M⦂ C) (n : ℕ) : ℕ → Set where
  sn : ({N : Γ ⊢M⦂ C} → M ↝ N → SNi↑ N n m) → #↑ M ≤ n → SNi↑ M n (suc m)

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

data SNₚ (P : Γ ⊢P⦂) : Set where
  sn : ({Q : Γ ⊢P⦂} → P ↝ₚ Q → SNₚ Q) → SNₚ P