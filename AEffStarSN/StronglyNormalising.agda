open import AEffStarSN.AEffStar

open import EffectAnnotations using (decₛ)

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _<_; _⊔_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⇒m≤o⊔n)
open import Data.List using (List) renaming ([] to []ₗ; _∷_ to _∷ₗ_; [_] to [_]ₗ; map to mapₗ; foldr to foldrₗ)

open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Function using (_∘_)

module AEffStarSN.StronglyNormalising where

variable
  B C : Set
  n m k : ℕ
  x y : B
  xs ys : List B

infix 4 _∈ₗ_
data _∈ₗ_ (x : B) : List B → Set where
  Hd : x ∈ₗ x ∷ₗ xs
  Tl : x ∈ₗ xs → x ∈ₗ y ∷ₗ xs

map-∈ₗ : {f : B → C} → x ∈ₗ xs → f x ∈ₗ mapₗ f xs
map-∈ₗ Hd = Hd
map-∈ₗ (Tl x) = Tl (map-∈ₗ x)

⊔-∈ₗ-≤ : x ∈ₗ xs → x ≤ foldrₗ _⊔_ 0 xs
⊔-∈ₗ-≤ Hd = m≤m⊔n _ _
⊔-∈ₗ-≤ (Tl p) = m≤n⇒m≤o⊔n _ (⊔-∈ₗ-≤ p)

data Reduct (M : Γ ⊢M⦂ X) : Set where
  r↝ : M ↝ N → Reduct M

ctx-↑ : Reduct M → Reduct (↑ op V M)
ctx-↑ (r↝ r) = r↝ (context-↑ r)

ctx-↓ : Reduct M → Reduct (↓ op V M)
ctx-↓ (r↝ r) = r↝ (context-T _ r)

ctx-promise : Reduct N → Reduct (promise op ↦ M `in N)
ctx-promise (r↝ r) = r↝ (context-promise r)

ctx-let : Reduct M → Reduct (let= M `in N)
ctx-let (r↝ r) = r↝ (context-T _ r)

reducts : (M : Γ ⊢M⦂ X) → List (Reduct M)
reducts (ƛ _ · _) =
  r↝ (apply _ _) ∷ₗ []ₗ
reducts (await ⟨ _ ⟩ until _) =
  r↝ (await-promise _ _) ∷ₗ []ₗ
reducts (let= return _ `in _) =
  r↝ (let-return _ _) ∷ₗ []ₗ
reducts (↓ _ _ (return _)) =
  r↝ (↓-return _ _) ∷ₗ []ₗ
reducts (promise _ ↦ _ `in ↑ _ _ _) =
  r↝ (promise-↑ _ _ _) ∷ₗ mapₗ ctx-promise (reducts _)
reducts (let= ↑ _ _ _ `in _) =
  r↝ (T-↑ _ _ _) ∷ₗ mapₗ ctx-let (reducts _)
reducts (let= promise _ ↦ _ `in _ `in _) =
  r↝ (T-promise _ _ _) ∷ₗ mapₗ ctx-let (reducts _)
reducts (let= await _ until _ `in _) =
  r↝ (T-await _ _ _) ∷ₗ mapₗ ctx-let (reducts _)
reducts (↓ _ _ (↑ _ _ _)) =
  r↝ (T-↑ _ _ _) ∷ₗ mapₗ ctx-↓ (reducts _)
reducts (↓ op _ (promise op' ↦ _ `in _)) with decₛ op op' | reducts _
... | yes refl | rec =
  r↝ (↓-promise-op _ _ _) ∷ₗ r↝ (T-promise _ _ _) ∷ₗ mapₗ ctx-↓ rec
... | no     a | rec =
  r↝ (T-promise _ _ _) ∷ₗ mapₗ ctx-↓ rec
reducts (↓ _ _ (await _ until _)) =
  r↝ (T-await _ _ _) ∷ₗ mapₗ ctx-↓ (reducts _)
reducts (promise _ ↦ _ `in _) =
  mapₗ ctx-promise (reducts _)
reducts (let= _ `in _) =
  mapₗ ctx-let (reducts _)
reducts (↓ _ _ _) =
  mapₗ ctx-↓ (reducts _)
reducts (↑ _ _ _) =
  mapₗ ctx-↑ (reducts _)
reducts _ =
  []ₗ

reducts-complete : (R : Reduct M) → R ∈ₗ reducts M
reducts-complete (r↝ (apply _ _)) = Hd
reducts-complete (r↝ (let-return _ _)) = Hd
reducts-complete (r↝ (T-↑ (Tl _) _ _)) = Hd
reducts-complete (r↝ (T-↑ (T↓ _ _) _ _)) = Hd
reducts-complete (r↝ (T-promise (Tl _) _ _)) = Hd
reducts-complete (r↝ (T-promise {op = op} (T↓ op' _) _ _)) with decₛ op' op
... | yes refl = Tl Hd
... | no     a = Hd
reducts-complete (r↝ (T-await (Tl _) _ _)) = Hd
reducts-complete (r↝ (T-await (T↓ _ _) _ _)) = Hd
reducts-complete (r↝ (promise-↑ _ _ _)) = Hd
reducts-complete (r↝ (↓-return _ _)) = Hd
reducts-complete (r↝ (↓-promise-op {op = op} _ _ _)) with decₛ op op
... | yes refl = Hd
... | no     a = ⊥-elim (a refl)
reducts-complete (r↝ (await-promise _ _)) = Hd
reducts-complete (r↝ (context-↑ r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = ↑ _ _ _} r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-promise {N = _ · _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = promise _ ↦ _ `in _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = await _ until _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = let= _ `in _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-promise {N = ↓ _ _ _} r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-T {M = _ · _} (Tl _) r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-T {M = ↑ _ _ _} (Tl _) r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-T {M = promise _ ↦ _ `in _} (Tl _) r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-T {M = await _ until _} (Tl _) r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-T {M = _ aT _} (Tl _) r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-T {M = _ · _} (T↓ _ _) r)) = map-∈ₗ (reducts-complete (r↝ r))
reducts-complete (r↝ (context-T {M = ↑ _ _ _} (T↓ _ _) r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-T {M = promise op' ↦ _ `in _} (T↓ op _) r)) with decₛ op op' | reducts-complete (r↝ r)
... | yes refl | rec = Tl (Tl (map-∈ₗ rec))
... | no     a | rec = Tl (map-∈ₗ rec)
reducts-complete (r↝ (context-T {M = await _ until _} (T↓ _ _) r)) = Tl (map-∈ₗ (reducts-complete (r↝ r)))
reducts-complete (r↝ (context-T {M = _ aT _} (T↓ _ _) r)) = map-∈ₗ (reducts-complete (r↝ r))

data SN (M : Γ ⊢M⦂ X) : Set where
  sn : ({N : Γ ⊢M⦂ X} → M ↝ N → SN N) → SN M

SN' : (M : Γ ⊢M⦂ X) → Set
SN' {Γ} {X} M = {N : Γ ⊢M⦂ X} → M ↝ N → SN N

sn'→sn : SN' M → SN M
sn'→sn s = sn s

sn→sn' : SN M → SN' M
sn→sn' (sn f) = f

data SNi (M : Γ ⊢M⦂ X) : ℕ → Set where
  sn : ({N : Γ ⊢M⦂ X} → M ↝ N → SNi N n) → SNi M (suc n)

max : SN M → ℕ
max (sn sM) = suc (foldrₗ _⊔_ 0 (mapₗ (λ {(r↝ r) → max (sM r)}) (reducts _)))

sni-≤ : n ≤ m → SNi M n → SNi M m
sni-≤ (s≤s p) (sn sM) = sn (sni-≤ p ∘ sM)

sn→sni : (s : SN M) → SNi M (max s)
sn→sni (sn sM) = sn (λ r → sni-≤ (⊔-∈ₗ-≤ (map-∈ₗ (reducts-complete (r↝ r)))) (sn→sni (sM r)))

#↑ : Γ ⊢M⦂ X → ℕ
#↑ (↑ _ _ M) = suc (#↑ M)
#↑ _ = 0

data SN↑ (M : Γ ⊢M⦂ X) (n : ℕ) : Set where
  sn : ({N : Γ ⊢M⦂ X} → M ↝ N → SN↑ N n) → #↑ M ≤ n → SN↑ M n

max↑ : SN M → ℕ
max↑ {M = M} (sn sM) = #↑ M ⊔ foldrₗ _⊔_ 0 (mapₗ (λ {(r↝ r) → max↑ (sM r)}) (reducts _))

sn↑-≤ : n ≤ m → SN↑ M n → SN↑ M m
sn↑-≤ p (sn sM q) = sn (sn↑-≤ p ∘ sM) (≤-trans q p)

sn→sn↑ : (s : SN M) → SN↑ M (max↑ s)
sn→sn↑ (sn sM) = sn (λ r → sn↑-≤ (m≤n⇒m≤o⊔n _ (⊔-∈ₗ-≤ (map-∈ₗ (reducts-complete (r↝ r))))) (sn→sn↑ (sM r))) (m≤m⊔n _ _)
