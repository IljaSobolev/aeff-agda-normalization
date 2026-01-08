open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; +-mono-≤-<; +-suc)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Induction.WellFounded using (Acc; acc)

open import AEffFinSN.AEff
open import AEffFinSN.StronglyNormalising using (SN; sn)
import AEffBaseSN.AEffBase.Types as B
import AEffBaseSN.AEffBase.AEff as B
import AEffBaseSN.AEffBase.Renamings as B
import AEffBaseSN.AEffBase.Substitutions as B
import AEffBaseSN.AEffBase.Preservation as B
import AEffBaseSN.AEffBase.Finality as B
open import AEffBaseSN.StronglyNormalising using () renaming (SN to SN*; sn to sn*)
open import AEffBaseSN.Main using () renaming (strong-norm to strong-norm*)
open import AEff.Simulation using (Context; [-]; coe; other; _↝c_; coe-ctx; other-ctx; coe-[-]; coe-↓; ∣_∣; size-mono-↝)

open import AEff.Types using (GType)

module AEffFinSN.Simulation where

-- EMBEDDING OF AEFF TYPES, CONTEXT, VARIABLES, TERMS INTO AEFFBASE

emb-ty-v : VType → B.Type

emb-ty-c : CType → B.Type

emb-ty-v (``` x) = B.``` x
emb-ty-v (X ⇒ C) = emb-ty-v X B.⇒ emb-ty-c C
emb-ty-v ⟨ X ⟩ = B.⟨ emb-ty-v X ⟩

emb-ty-c (X ! _) = emb-ty-v X

emb-ctx : Ctx → B.Ctx
emb-ctx [] = B.[]
emb-ctx (Γ ∷ X) = emb-ctx Γ B.∷ emb-ty-v X

emb-∈ : X ∈ Γ → emb-ty-v X B.∈ emb-ctx Γ
emb-∈ Hd = B.Hd
emb-∈ (Tl x) = B.Tl (emb-∈ x)

emb-tm-v : Γ ⊢V⦂ X → emb-ctx Γ B.⊢V⦂ emb-ty-v X

emb-tm-m : Γ ⊢M⦂ C → emb-ctx Γ B.⊢M⦂ emb-ty-c C

emb-tm-v (` x) = B.` emb-∈ x
emb-tm-v (`` c) = B.`` c
emb-tm-v (ƛ M) = B.ƛ (emb-tm-m M)
emb-tm-v ⟨ V ⟩ = B.⟨ emb-tm-v V ⟩

emb-tm-m (return V) = B.return (emb-tm-v V)
emb-tm-m (V · W) = emb-tm-v V B.· emb-tm-v W
emb-tm-m (let= M `in N) = B.let= (emb-tm-m M) `in (emb-tm-m N)
emb-tm-m (↑ op V M) = B.↑ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (↓ {C = _ ! _} op V M) = B.↓ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (promise op ∣ p , q ↦ M `in N) = B.promise op ↦ emb-tm-m M `in emb-tm-m N
emb-tm-m (await V until N) = B.await emb-tm-v V until emb-tm-m N
emb-tm-m (coerce p M) = emb-tm-m M


-- RELATION BETWEEN AEFF RENAMINGS AND AEFFBASE RENAMINGS

infix 4 _~ᵣ_
_~ᵣ_ : (r : Ren Γ Δ) (r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)) → Set
r ~ᵣ r† = {X : VType} (x : X ∈ _) → emb-∈ (r x) ≡ r† (emb-∈ x)


-- RELATED RENAMINGS ACT THE SAME ON EMBEDDED TERMS

~ᵣ-v : (V : Γ ⊢V⦂ X) →
       {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
       r ~ᵣ r† →
       ------------
       emb-tm-v (V-rename r V) ≡ B.V-rename r† (emb-tm-v V)

~ᵣ-m : (M : Γ ⊢M⦂ C)
       {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
       r ~ᵣ r† →
       ------------
       emb-tm-m (M-rename r M) ≡ B.M-rename r† (emb-tm-m M)

~ᵣ-lift : (M : Γ ∷ X ⊢M⦂ C)
          {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
          r ~ᵣ r† →
          ------------
          emb-tm-m (M-rename (wk₂ r) M) ≡ B.M-rename (B.wk₂ r†) (emb-tm-m M)
~ᵣ-lift M ~r = ~ᵣ-m M (λ {Hd → refl; (Tl x) → cong B.Tl (~r x)})

~ᵣ-v (` x) ~r = cong B.`_ (~r x)
~ᵣ-v (`` c) ~r = refl
~ᵣ-v (ƛ M) ~r = cong B.ƛ (~ᵣ-lift M ~r)
~ᵣ-v ⟨ V ⟩ ~r = cong B.⟨_⟩ (~ᵣ-v V ~r)

~ᵣ-m (return V) ~r = cong B.return (~ᵣ-v V ~r)
~ᵣ-m (let= M `in N) ~r = cong₂ B.let=_`in_ (~ᵣ-m M ~r) (~ᵣ-lift N ~r)
~ᵣ-m (V · W) ~r = cong₂ B._·_ (~ᵣ-v V ~r) (~ᵣ-v W ~r)
~ᵣ-m (↑ op V M) ~r = cong₂ (B.↑ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (↓ {C = _ ! _} op V M) ~r = cong₂ (B.↓ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (promise op ∣ p , q ↦ M `in N) ~r = cong₂ (B.promise op ↦_`in_) (~ᵣ-lift M ~r) (~ᵣ-lift N ~r)
~ᵣ-m (await V until N) ~r = cong₂ (B.await_until_) (~ᵣ-v V ~r) (~ᵣ-lift N ~r)
~ᵣ-m (coerce p M) ~r = ~ᵣ-m M ~r


-- RELATION BETWEEN AEFF SUBSTITUTIONS AND AEFFBASE SUBSTITUTIONS

infix 4 _~ₛ_
_~ₛ_ : (s : Sub Γ Δ) (s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)) → Set
s ~ₛ s† = {X : VType} (x : X ∈ _) → emb-tm-v (s x) ≡ s† (emb-∈ x)


-- RELATED SUBSTITUTIONS ACT THE SAME ON EMBEDDED TERMS

~ₛ-v : (V : Γ ⊢V⦂ X)
       {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
       s ~ₛ s† →
       ------------
       emb-tm-v (V [ s ]v) ≡ emb-tm-v V B.[ s† ]v

~ₛ-m : (M : Γ ⊢M⦂ C)
       {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
       s ~ₛ s† →
       ------------
       emb-tm-m (M [ s ]m) ≡ emb-tm-m M B.[ s† ]m

~ₛ-lift : (M : Γ ∷ X ⊢M⦂ C)
          {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
          s ~ₛ s† →
          ------------
          emb-tm-m (M [ lift s ]m) ≡ (emb-tm-m M) B.[ B.lift s† ]m
~ₛ-lift M ~s = ~ₛ-m M (λ {Hd → refl; (Tl x) → trans (~ᵣ-v _ (λ _ → refl)) (cong (B.V-rename B.Tl) (~s x))})

~ₛ-v (` x) ~s = ~s x
~ₛ-v (`` c) ~s = refl
~ₛ-v (ƛ M) ~s = cong B.ƛ (~ₛ-lift M ~s)
~ₛ-v ⟨ V ⟩ ~s = cong B.⟨_⟩ (~ₛ-v V ~s)

~ₛ-m (return V) ~s = cong B.return (~ₛ-v V ~s)
~ₛ-m (let= M `in N) ~s = cong₂ B.let=_`in_ (~ₛ-m M ~s) (~ₛ-lift N ~s)
~ₛ-m (V · W) ~s = cong₂ B._·_ (~ₛ-v V ~s) (~ₛ-v W ~s)
~ₛ-m (↑ op V M) ~s = cong₂ (B.↑ op) (~ₛ-v V ~s) (~ₛ-m M ~s)
~ₛ-m (↓ {C = _ ! _} op V M) ~s = cong₂ (B.↓ op) (~ₛ-v V ~s) (~ₛ-m M ~s)
~ₛ-m (promise op ∣ p , q ↦ M `in N) ~s = cong₂ (B.promise op ↦_`in_) (~ₛ-lift M ~s) (~ₛ-lift N ~s)
~ₛ-m (await V until N) ~s = cong₂ (B.await_until_) (~ₛ-v V ~s) (~ₛ-lift N ~s)
~ₛ-m (coerce p M) ~s = ~ₛ-m M ~s

~ᵣ-wk₁-v : (V : Γ ⊢V⦂ X) →
           -----------
           emb-tm-v (V-rename (wk₁ {X = Z}) V) ≡ B.V-rename B.wk₁ (emb-tm-v V)
~ᵣ-wk₁-v V = ~ᵣ-v V (λ _ → refl)

~ᵣ-wk₂-wk₁-m : (M : Γ ∷ X ⊢M⦂ C) →
               -----------
               emb-tm-m (M-rename (wk₂ (wk₁ {X = Z})) M) ≡ B.M-rename (B.wk₂ B.wk₁) (emb-tm-m M)
~ᵣ-wk₂-wk₁-m M = ~ᵣ-m M (λ {Hd → refl; (Tl x) → refl})

~ₛᵣ-m : (M : Γ ∷ X ⊢M⦂ C) (V : Γ ⊢V⦂ X) →
        -----------
        emb-tm-m (M [ id-subst [ V ]s ]m) ≡ emb-tm-m M B.[ B.id-subst B.[ emb-tm-v V ]s ]m
~ₛᵣ-m M V = ~ₛ-m M (λ {Hd → refl; (Tl x) → refl})

~-strengthen : {A : GType} (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A) →
               -----------------------
               emb-tm-v (strengthen-val V) ≡ B.strengthen-val (emb-tm-v V)
~-strengthen (` Tl x) = refl
~-strengthen (`` c) = refl


-- SINCE AEFFBASE DOESN'T HAVE COERCION, WE HAVE TO KEEP TRACK OF REDUCTIONS
-- INVOLVING COERCE TERMS USING EVALUATION CONTEXTS

find-ctx : {Γ : Ctx} {X : CType} → Γ ⊢M⦂ X → Context
find-ctx (return _) = [-]
find-ctx (let= M `in _) = other (find-ctx M)
find-ctx (_ · _) = [-]
find-ctx (↑ _ _ M) = other (find-ctx M)
find-ctx (↓ _ _ M) = other (find-ctx M)
find-ctx (promise _ ∣ _ , _ ↦ _ `in N) = other (find-ctx N)
find-ctx (await _ until M) = [-]
find-ctx (coerce _ M) = coe (find-ctx M)


-- THE SIMULATION RESULT: A REDUCTION IN AEFFFIN EITHER CORRESPONDS TO A REDUCTION IN AEFFBASE
-- OR IT IS THE REDUCTION OF THE EVALUATION CONTEXT

sim : M ↝↝ N → emb-tm-m M B.↝↝ emb-tm-m N ⊎ (emb-tm-m M ≡ emb-tm-m N) × find-ctx M ↝c find-ctx N
sim (apply M V) rewrite ~ₛᵣ-m M V = inj₁ (B.apply _ _)
sim (let-return V N) rewrite ~ₛᵣ-m N V = inj₁ (B.let-return _ _)
sim (let-↑ V M N) = inj₁ (B.let-↑ _ _ _)
sim (let-promise {X = X} p q M₁ M₂ N) rewrite ~ᵣ-wk₂-wk₁-m {Z = ⟨ X ⟩} N = inj₁ (B.let-promise _ _ _)
sim (promise-↑ p q V M N) rewrite ~-strengthen V = inj₁ (B.promise-↑ _ _ _)
sim (↓-return V W) = inj₁ (B.↓-return _ _)
sim (↓-↑ V W M) = inj₁ (B.↓-↑ _ _ _)
sim (↓-promise-op {X = X} p q V M N) rewrite ~ₛᵣ-m M V | ~ᵣ-wk₁-v {Z = ⟨ X ⟩} V = inj₁ (B.↓-promise-op _ _ _)
sim (↓-promise-op' {X = X} V p q r M N) rewrite ~ᵣ-wk₁-v {Z = ⟨ X ⟩} V = inj₁ (B.↓-promise-op' (λ z → r (sym z)) _ _ _)
sim (let-await {X = X} V M N) rewrite ~ᵣ-wk₂-wk₁-m {Z = X} N = inj₁ (B.let-await _ _ _)
sim (↓-await {X = X} {_ ! _} W V M) rewrite ~ᵣ-wk₁-v {Z = X} W = inj₁ (B.↓-await _ _ _)
sim (await-promise V N) rewrite ~ₛᵣ-m N V = inj₁ (B.await-promise _ _)
sim (context-let r) with sim r
... | inj₁ r = inj₁ (B.context-let r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-↑ r) with sim r
... | inj₁ r = inj₁ (B.context-↑ r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-↓ {_} {_ ! _} r) with sim r
... | inj₁ r = inj₁ (B.context-↓ r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-promise r) with sim r
... | inj₁ r = inj₁ (B.context-promise r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-coerce r) with sim r
... | inj₁ r = inj₁ r
... | inj₂ (e , r) rewrite e = inj₂ (refl , coe-ctx r)
sim (coerce-return V) = inj₂ (refl , coe-[-])
sim (coerce-↑ V M) = inj₂ (refl , coe-↓)
sim (coerce-promise x p q M N) = inj₂ (refl , coe-↓)


-- STRONG NORMALISATION PROOF BY MEANS OF THE SIMULATION

sn*→sn : Acc _<_ ∣ find-ctx M ∣ → SN* (emb-tm-m M) → M ↝↝ N → SN N
sn*→sn aM sM r with sim r
sn*→sn aM (sn* f) _ | inj₁ r = sn (sn*→sn (<-wellFounded _) (f r))
sn*→sn (acc aM) sM _ | inj₂ (e , r) rewrite e = sn (sn*→sn (aM (size-mono-↝ r)) sM)

strong-norm : (M : Γ ⊢M⦂ C) → SN M
strong-norm M = sn (sn*→sn (<-wellFounded _) (strong-norm* (emb-tm-m M)))