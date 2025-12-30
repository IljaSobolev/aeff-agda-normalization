import AEffStarSN.AEffStar as B
open import AEffStarSN.StronglyNormalising renaming (SN to SN*)
open import AEffStarSN.Main renaming (strong-norm to strong-norm*)

open import Types
open import AEff
open import Preservation
open import Finality
open import Renamings
open import Substitutions
open import EffectAnnotations

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; +-mono-≤-<; +-suc)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List renaming (_∷_ to _∷ₗ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)

module Simulation where

emb-ty-v : VType → B.Type

emb-ty-c : CType → B.Type

emb-ty-v (``` x) = B.``` x
emb-ty-v (X ⇒ Y) = emb-ty-v X B.⇒ emb-ty-c Y
emb-ty-v ⟨ V ⟩ = B.⟨ emb-ty-v V ⟩

emb-ty-c (X ! _) = emb-ty-v X

emb-ctx : Ctx → B.Ctx
emb-ctx [] = B.[]
emb-ctx (Γ ∷ X) = emb-ctx Γ B.∷ emb-ty-v X

emb-∈ : {Γ : Ctx} {X : VType} → X ∈ Γ → emb-ty-v X B.∈ emb-ctx Γ
emb-∈ Hd = B.Hd
emb-∈ (Tl x) = B.Tl (emb-∈ x)

emb-tm-v : {Γ : Ctx} {X : VType} → Γ ⊢V⦂ X → emb-ctx Γ B.⊢V⦂ emb-ty-v X

emb-tm-m : {Γ : Ctx} {X : CType} → Γ ⊢M⦂ X → emb-ctx Γ B.⊢M⦂ emb-ty-c X

emb-tm-v (` x) = B.` (emb-∈ x)
emb-tm-v (`` c) = B.`` c
emb-tm-v (ƛ M) = B.ƛ (emb-tm-m M)
emb-tm-v ⟨ V ⟩ = B.⟨ emb-tm-v V ⟩

emb-tm-m (return V) = B.return (emb-tm-v V)
emb-tm-m (let= M `in N) = B.let= emb-tm-m M `in emb-tm-m N
emb-tm-m (V · W) = emb-tm-v V B.· emb-tm-v W
emb-tm-m (↑ op p V M) = B.↑ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (↓ op V M) = B.↓ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (promise op ∣ p ↦ M `in N) = B.promise op ↦ emb-tm-m M `in emb-tm-m N
emb-tm-m (await V until M) = B.await emb-tm-v V until emb-tm-m M
emb-tm-m (coerce p q M) = emb-tm-m M

infix 4 _~-ren_
_~-ren_ : {Γ Δ : Ctx} (r : Ren Γ Δ) (r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)) → Set
_~-ren_ {Γ} r r† = {X : VType} (x : X ∈ Γ) → emb-∈ (r x) ≡ r† (emb-∈ x)

infix 4 _~-sub_
_~-sub_ : {Γ Δ : Ctx} (s : Sub Γ Δ) (r† : B.Sub (emb-ctx Γ) (emb-ctx Δ)) → Set
_~-sub_ {Γ} s s† = {X : VType} (x : X ∈ Γ) → emb-tm-v (s x) ≡ s† (emb-∈ x)

~-ren-v : {Γ Δ : Ctx} {X : VType} (V : Γ ⊢V⦂ X)
          {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
          r ~-ren r† →
          ------------
          emb-tm-v (V-rename r V) ≡ B.V-rename r† (emb-tm-v V)

~-ren-m : {Γ Δ : Ctx} {X : CType} (M : Γ ⊢M⦂ X)
          {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
          r ~-ren r† →
          ------------
          emb-tm-m (M-rename r M) ≡ B.M-rename r† (emb-tm-m M)

~-ren-lift : {Γ Δ : Ctx} {X : VType} {Y : CType} (M : Γ ∷ X ⊢M⦂ Y)
             {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
             r ~-ren r† →
             ------------
             emb-tm-m (M-rename (wk₂ r) M) ≡ B.M-rename (B.wk₂ r†) (emb-tm-m M)
~-ren-lift M ~r = ~-ren-m M (λ {Hd → refl; (Tl x) → cong B.Tl (~r x)})

~-ren-v (` x) ~r = cong B.`_ (~r x)
~-ren-v (`` c) ~r = refl
~-ren-v (ƛ M) ~r = cong B.ƛ (~-ren-lift M ~r)
~-ren-v ⟨ V ⟩ ~r = cong B.⟨_⟩ (~-ren-v V ~r)

~-ren-m (return V) ~r = cong B.return (~-ren-v V ~r)
~-ren-m (let= M `in N) ~r = cong₂ B.let=_`in_ (~-ren-m M ~r) (~-ren-lift N ~r)
~-ren-m (V · W) ~r = cong₂ B._·_ (~-ren-v V ~r) (~-ren-v W ~r)
~-ren-m (↑ op p V M) ~r = cong₂ (B.↑ op) (~-ren-v V ~r) (~-ren-m M ~r)
~-ren-m (↓ op V M) ~r = cong₂ (B.↓ op) (~-ren-v V ~r) (~-ren-m M ~r)
~-ren-m (promise op ∣ p ↦ M `in N) ~r = cong₂ (B.promise op ↦_`in_) (~-ren-lift M ~r) (~-ren-lift N ~r)
~-ren-m (await V until M) ~r = cong₂ B.await_until_ (~-ren-v V ~r) (~-ren-lift M ~r)
~-ren-m (coerce p q M) ~r = ~-ren-m M ~r

~-sub-v : {Γ Δ : Ctx} {X : VType} (V : Γ ⊢V⦂ X)
          {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
          s ~-sub s† →
          ------------
          emb-tm-v (V [ s ]v) ≡ (emb-tm-v V) B.[ s† ]v

~-sub-m : {Γ Δ : Ctx} {X : CType} (M : Γ ⊢M⦂ X)
          {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
          s ~-sub s† →
          ------------
          emb-tm-m (M [ s ]m) ≡ (emb-tm-m M) B.[ s† ]m

~-lift : {Γ Δ : Ctx} {X : VType}
         {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
         s ~-sub s† →
         ----------
         lift {X = X} s ~-sub B.lift s†
~-lift ~s Hd = refl
~-lift {s = s} ~s (Tl x) rewrite sym (~s x) = ~-ren-v (s x) (λ {Hd → refl; (Tl x) → refl})

~-sub-lift : {Γ Δ : Ctx} {X : VType} {Y : CType} (M : Γ ∷ X ⊢M⦂ Y)
             {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
             s ~-sub s† →
             ------------
             emb-tm-m (M [ lift s ]m) ≡ (emb-tm-m M) B.[ B.lift s† ]m
~-sub-lift M ~s = ~-sub-m M (~-lift ~s)

~-sub-v (` x) ~s = ~s x
~-sub-v (`` c) ~r = refl
~-sub-v (ƛ M) ~r = cong B.ƛ (~-sub-lift M ~r)
~-sub-v ⟨ V ⟩ ~r = cong B.⟨_⟩ (~-sub-v V ~r)

~-sub-m (return V) ~r = cong B.return (~-sub-v V ~r)
~-sub-m (let= M `in N) ~r = cong₂ B.let=_`in_ (~-sub-m M ~r) (~-sub-lift N ~r)
~-sub-m (V · W) ~r = cong₂ B._·_ (~-sub-v V ~r) (~-sub-v W ~r)
~-sub-m (↑ op p V M) ~r = cong₂ (B.↑ op) (~-sub-v V ~r) (~-sub-m M ~r)
~-sub-m (↓ op V M) ~r = cong₂ (B.↓ op) (~-sub-v V ~r) (~-sub-m M ~r)
~-sub-m (promise op ∣ p ↦ M `in N) ~r = cong₂ (B.promise op ↦_`in_) (~-sub-lift M ~r) (~-sub-lift N ~r)
~-sub-m (await V until M) ~r = cong₂ B.await_until_ (~-sub-v V ~r) (~-sub-lift M ~r)
~-sub-m (coerce p q M) ~r = ~-sub-m M ~r

~-rename-v : {Γ : Ctx} {X Z : VType}
             (V : Γ ⊢V⦂ X) →
             -----------
             emb-tm-v (V-rename (wk₁ {X = Z}) V) ≡ B.V-rename (B.wk₁) (emb-tm-v V)
~-rename-v V = ~-ren-v V (λ {Hd → refl; (Tl x) → refl})

~-rename-m : {Γ : Ctx} {X Z : VType} {Y : CType}
             (M : Γ ∷ X ⊢M⦂ Y) →
             -----------
             emb-tm-m (M-rename (wk₂ (wk₁ {X = Z})) M) ≡ B.M-rename (B.wk₂ B.wk₁) (emb-tm-m M)
~-rename-m M = ~-ren-m M (λ {Hd → refl; (Tl x) → refl})

~-subst-m : {Γ : Ctx} {X : VType} {Y : CType}
            (M : Γ ∷ X ⊢M⦂ Y) (V : Γ ⊢V⦂ X) →
            -----------
            emb-tm-m (M [ id-subst [ V ]s ]m) ≡ (emb-tm-m M) B.[ B.ids B.[ emb-tm-v V ]s ]m
~-subst-m M V = ~-sub-m M (λ {Hd → refl; (Tl x) → refl})

~-strengthen : {Γ : Ctx} {X : VType} {A : BType}
               (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A) →
               -----------------------
               emb-tm-v (strengthen-val {Δ = X ∷ₗ []} V) ≡ B.strengthen-val {X = emb-ty-v X} (emb-tm-v V)
~-strengthen (` Tl x) = refl
~-strengthen (`` c) = refl

data Context : Set where
  [-] : Context
  coe other : Context → Context

variable
  CC CC' : Context

infix 4 _↝c_
data _↝c_ : Context → Context → Set where
  coe-[-] : coe [-] ↝c [-]
  coe-↓ : coe (other CC) ↝c other (coe CC)
  coe-ctx : CC ↝c CC' → coe CC ↝c coe CC'
  other-ctx : CC ↝c CC' → other CC ↝c other CC'

find-ctx : {Γ : Ctx} {X : CType} → Γ ⊢M⦂ X → Context
find-ctx (return _) = [-]
find-ctx (let= M `in _) = other (find-ctx M)
find-ctx (_ · _) = [-]
find-ctx (↑ _ _ _ M) = other (find-ctx M)
find-ctx (↓ _ _ M) = other (find-ctx M)
find-ctx (promise _ ∣ _ ↦ _ `in N) = other (find-ctx N)
find-ctx (await _ until M) = [-]
find-ctx (coerce _ _ M) = coe (find-ctx M)

sim : {Γ : Ctx} {X : CType} {M N : Γ ⊢M⦂ X} →
      M ↝↝ N →
      ------------------------
      emb-tm-m M B.↝ emb-tm-m N ⊎ (emb-tm-m M ≡ emb-tm-m N) × find-ctx M ↝c find-ctx N
sim (apply M V) rewrite ~-subst-m M V = inj₁ (B.apply _ _)
sim (let-return V N) rewrite ~-subst-m N V = inj₁ (B.let-return _ _)
sim (let-↑ p V M N) = inj₁ (B.T-↑ _ _ _)
sim (let-promise {X} p M₁ M₂ N) rewrite ~-rename-m {Z = ⟨ X ⟩} N = inj₁ (B.T-promise _ _ _)
sim (promise-↑ p q V M N) rewrite ~-strengthen V = inj₁ (B.promise-↑ _ _ _)
sim (↓-return V W) = inj₁ (B.↓-return _ _)
sim (↓-↑ p V W M) = inj₁ (B.T-↑ _ _ _)
sim (↓-promise-op {X} p V M N) rewrite ~-subst-m M V | ~-rename-v {Z = ⟨ X ⟩} V = inj₁ (B.↓-promise-op _ _ _)
sim (↓-promise-op' {X} p q V M N) rewrite ~-rename-v {Z = ⟨ X ⟩} V = inj₁ (B.T-promise _ _ _)
sim (await-promise V M) rewrite ~-subst-m M V = inj₁ (B.await-promise _ _)
sim (context-let r) with sim r
... | inj₁ r = inj₁ (B.context-T _ r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-↑ r) with sim r
... | inj₁ r = inj₁ (B.context-↑ r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-↓ r) with sim r
... | inj₁ r = inj₁ (B.context-T _ r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-promise r) with sim r
... | inj₁ r = inj₁ (B.context-promise r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-coerce r) with sim r
... | inj₁ r = inj₁ r
... | inj₂ (e , r) rewrite e = inj₂ (refl , coe-ctx r)
sim (coerce-return V) = inj₂ (refl , coe-[-])
sim (coerce-↑ r V M) = inj₂ (refl , coe-↓)
sim (coerce-promise r M N) = inj₂ (refl , coe-↓)

height : Context → ℕ
height [-] = zero
height (coe CC) = suc (height CC)
height (other CC) = suc (height CC)

∣_∣ : Context → ℕ
∣ [-] ∣ = 0
∣ coe CC ∣ = height CC + suc ∣ CC ∣
∣ other CC ∣ = suc ∣ CC ∣

height-mono-↝ : CC ↝c CC' → height CC' ≤ height CC
height-mono-↝ coe-[-] = z≤n
height-mono-↝ coe-↓ = ≤-refl
height-mono-↝ (coe-ctx r) = s≤s (height-mono-↝ r)
height-mono-↝ (other-ctx r) = s≤s (height-mono-↝ r)

size-mono-↝ : CC ↝c CC' → ∣ CC' ∣ < ∣ CC ∣
size-mono-↝ coe-[-] = s≤s z≤n
size-mono-↝ coe-↓ = s≤s (≤-reflexive (sym (+-suc _ _)))
size-mono-↝ (coe-ctx r) = +-mono-≤-< (height-mono-↝ r) (s≤s (size-mono-↝ r))
size-mono-↝ (other-ctx r) = s≤s (size-mono-↝ r)

data SN {Γ : Ctx} {X : CType} (M : Γ ⊢M⦂ X) : Set where
  sn : ({N : Γ ⊢M⦂ X} → M ↝↝ N → SN N) → SN M

sn*→sn : {Γ : Ctx} {X : CType} {M N : Γ ⊢M⦂ X} →
         Acc _<_ ∣ find-ctx M ∣ →
         --------------------------------
         SN* (emb-tm-m M) → M ↝↝ N → SN N
sn*→sn aM sM r with sim r
sn*→sn aM (sn f) _ | inj₁ r = sn (sn*→sn (<-wellFounded _) (f r))
sn*→sn (acc aM) sM _ | inj₂ (e , r) rewrite e = sn (sn*→sn (aM (size-mono-↝ r)) sM)

strong-norm : {Γ : Ctx} {X : CType} (M : Γ ⊢M⦂ X) → SN M
strong-norm M = sn (sn*→sn (<-wellFounded _) (strong-norm* (emb-tm-m M)))