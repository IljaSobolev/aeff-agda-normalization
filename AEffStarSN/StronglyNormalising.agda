open import AEffStarSN.AEffStar

open import EffectAnnotations using (decₛ)

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _<_; _⊔_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⇒m≤o⊔n)
open import Data.List using (List) renaming ([] to []ₗ; _∷_ to _∷ₗ_; _++_ to _++ₗ_; [_] to [_]ₗ; map to mapₗ; foldr to foldrₗ)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

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

++-∈ₗ : x ∈ₗ xs ⊎ x ∈ₗ ys → x ∈ₗ xs ++ₗ ys
++-∈ₗ {xs = []ₗ} (inj₂ x) = x
++-∈ₗ {xs = _ ∷ₗ _} (inj₁ Hd) = Hd
++-∈ₗ {xs = _ ∷ₗ _} (inj₁ (Tl x)) = Tl (++-∈ₗ (inj₁ x))
++-∈ₗ {xs = _ ∷ₗ _} (inj₂ x) = Tl (++-∈ₗ (inj₂ x))

⊔-∈ₗ-≤ : x ∈ₗ xs → x ≤ foldrₗ _⊔_ 0 xs
⊔-∈ₗ-≤ Hd = m≤m⊔n _ _
⊔-∈ₗ-≤ (Tl p) = m≤n⇒m≤o⊔n _ (⊔-∈ₗ-≤ p)

data Reduct (M : Γ ⊢M⦂ X) : Set where
  r↝ : M ↝ N → Reduct M

reducts-base : (M : Γ ⊢M⦂ X) → List (Reduct M)
reducts-base (ƛ _ · _) = [ r↝ (apply _ _) ]ₗ
reducts-base (await ⟨ _ ⟩ until _) = [ r↝ (await-promise _ _) ]ₗ
reducts-base (let= return _ `in _) = [ r↝ (let-return _ _) ]ₗ
reducts-base (↓ _ _ (return _)) = [ r↝ (↓-return _ _) ]ₗ
reducts-base (promise _ ↦ _ `in ↑ _ _ _) = [ r↝ (promise-↑ _ _ _) ]ₗ
reducts-base (let= ↑ _ _ _ `in _) = [ r↝ (let-↑ _ _ _) ]ₗ
reducts-base (let= promise _ ↦ _ `in _ `in _) = [ r↝ (let-promise _ _ _) ]ₗ
reducts-base (let= await _ until _ `in _) = [ r↝ (let-await _ _ _) ]ₗ
reducts-base (↓ _ _ (↑ _ _ _)) = [ r↝ (↓-↑ _ _ _) ]ₗ
reducts-base (↓ op _ (promise op' ↦ _ `in _)) with decₛ op' op
... | yes refl = [ r↝ (↓-promise-op _ _ _) ]ₗ
... | no     p = [ r↝ (↓-promise-op' p _ _ _) ]ₗ
reducts-base (↓ _ _ (await _ until _)) = [ r↝ (↓-await _ _ _) ]ₗ
reducts-base _ = []ₗ

ctx-↑ : Reduct M → Reduct (↑ op V M)
ctx-↑ (r↝ r) = r↝ (context-↑ r)

ctx-↓ : Reduct M → Reduct (↓ op V M)
ctx-↓ (r↝ r) = r↝ (context-↓ r)

ctx-promise : Reduct N → Reduct (promise op ↦ M `in N)
ctx-promise (r↝ r) = r↝ (context-promise r)

ctx-let : Reduct M → Reduct (let= M `in N)
ctx-let (r↝ r) = r↝ (context-let r)

reducts-ctx : (M : Γ ⊢M⦂ X) → List (Reduct M)
reducts-ctx (return _) = []ₗ
reducts-ctx (_ · _) = []ₗ
reducts-ctx (let= M `in _) = mapₗ ctx-let (reducts-base M ++ₗ reducts-ctx M)
reducts-ctx (↑ _ _ M) = mapₗ ctx-↑ (reducts-base M ++ₗ reducts-ctx M)
reducts-ctx (↓ _ _ M) = mapₗ ctx-↓ (reducts-base M ++ₗ reducts-ctx M)
reducts-ctx (promise _ ↦ _ `in N) = mapₗ ctx-promise (reducts-base N ++ₗ reducts-ctx N)
reducts-ctx (await _ until _) = []ₗ

reducts-complete' : (R : Reduct M) → R ∈ₗ reducts-base M ⊎ R ∈ₗ reducts-ctx M
reducts-complete' (r↝ (apply M V)) = inj₁ Hd
reducts-complete' (r↝ (let-return V N)) = inj₁ Hd
reducts-complete' (r↝ (let-↑ N V M)) = inj₁ Hd
reducts-complete' (r↝ (↓-↑ V' V M)) = inj₁ Hd
reducts-complete' (r↝ (promise-↑ V M N)) = inj₁ Hd
reducts-complete' (r↝ (↓-return V W)) = inj₁ Hd
reducts-complete' (r↝ (let-promise L M N)) = inj₁ Hd
reducts-complete' (r↝ (↓-promise-op {op = op} V M N)) with decₛ op op
... | yes refl = inj₁ Hd
... | no     p = ⊥-elim (p refl)
reducts-complete' (r↝ (↓-promise-op' {op = op} {op'} p V M N)) with decₛ op op'
... | yes refl = ⊥-elim (p refl)
... | no     p = inj₁ Hd
reducts-complete' (r↝ (let-await N V M)) = inj₁ Hd
reducts-complete' (r↝ (↓-await W V M)) = inj₁ Hd
reducts-complete' (r↝ (await-promise V M)) = inj₁ Hd
reducts-complete' (r↝ (context-↑ r)) = inj₂ (map-∈ₗ (++-∈ₗ (reducts-complete' (r↝ r))))
reducts-complete' (r↝ (context-promise r)) = inj₂ (map-∈ₗ (++-∈ₗ (reducts-complete' (r↝ r))))
reducts-complete' (r↝ (context-let r)) = inj₂ (map-∈ₗ (++-∈ₗ (reducts-complete' (r↝ r))))
reducts-complete' (r↝ (context-↓ r)) = inj₂ (map-∈ₗ (++-∈ₗ (reducts-complete' (r↝ r))))

reducts : (M : Γ ⊢M⦂ X) → List (Reduct M)
reducts M = reducts-base M ++ₗ reducts-ctx M

reducts-complete : (R : Reduct M) → R ∈ₗ reducts M
reducts-complete R = ++-∈ₗ (reducts-complete' R)

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
sni-≤ (s≤s p) (sn sM) = sn (λ r → sni-≤ p (sM r))

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
sn↑-≤ p (sn sM q) = sn (λ r → sn↑-≤ p (sM r)) (≤-trans q p)

sn→sn↑ : (s : SN M) → SN↑ M (max↑ s)
sn→sn↑ (sn sM) = sn (λ r → sn↑-≤ (m≤n⇒m≤o⊔n _ (⊔-∈ₗ-≤ (map-∈ₗ (reducts-complete (r↝ r))))) (sn→sn↑ (sM r))) (m≤m⊔n _ _)