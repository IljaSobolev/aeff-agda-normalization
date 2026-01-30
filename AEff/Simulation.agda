open import AEff.Types
open import AEff.AEff
open import AEff.Preservation
open import AEff.Finality
open import AEff.Renamings
open import AEff.Substitutions
open import AEff.EffectAnnotations

import AEffBaseSN.AEffBase.Types as B
import AEffBaseSN.AEffBase.AEff as B
import AEffBaseSN.AEffBase.Renamings as B
import AEffBaseSN.AEffBase.Substitutions as B
import AEffBaseSN.AEffBase.Preservation as B
import AEffBaseSN.AEffBase.Finality as B

open import AEffBaseSN.StronglyNormalising using () renaming (SN to SN*; sn to sn*)
open import AEffBaseSN.Main using () renaming (strong-norm to strong-norm*)

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; +-mono-≤-<; +-suc)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using () renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

module AEff.Simulation where

-- EMBEDDING OF AEFF TYPES, CONTEXTS, VARIABLES AND TERMS INTO AEFFBASE

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


-- RELATION BETWEEN AEFF RENAMINGS AND AEFFBASE RENAMINGS

infix 4 _~ᵣ_
_~ᵣ_ : {Γ Δ : Ctx} (r : Ren Γ Δ) (r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)) → Set
_~ᵣ_ {Γ} r r† = {X : VType} (x : X ∈ Γ) → emb-∈ (r x) ≡ r† (emb-∈ x)


-- RELATION BETWEEN AEFF SUBSTITUTIONS AND AEFFBASE SUBSTITUTIONS

infix 4 _~ₛ_ _~ₛ_
_~ₛ_ : {Γ Δ : Ctx} (s : Sub Γ Δ) (r† : B.Sub (emb-ctx Γ) (emb-ctx Δ)) → Set
_~ₛ_ {Γ} s s† = {X : VType} (x : X ∈ Γ) → emb-tm-v (s x) ≡ s† (emb-∈ x)


-- RELATED RENAMINGS ACT THE SAME ON RELATED TERMS

~ᵣ-v : {Γ Δ : Ctx} {X : VType} (V : Γ ⊢V⦂ X)
       {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
       r ~ᵣ r† →
       ------------
       emb-tm-v (V-rename r V) ≡ B.V-rename r† (emb-tm-v V)

~ᵣ-m : {Γ Δ : Ctx} {X : CType} (M : Γ ⊢M⦂ X)
       {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
       r ~ᵣ r† →
       ------------
       emb-tm-m (M-rename r M) ≡ B.M-rename r† (emb-tm-m M)

~ᵣ-lift : {Γ Δ : Ctx} {X : VType} {Y : CType} (M : Γ ∷ X ⊢M⦂ Y)
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
~ᵣ-m (↑ op p V M) ~r = cong₂ (B.↑ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (↓ op V M) ~r = cong₂ (B.↓ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (promise op ∣ p ↦ M `in N) ~r = cong₂ (B.promise op ↦_`in_) (~ᵣ-lift M ~r) (~ᵣ-lift N ~r)
~ᵣ-m (await V until M) ~r = cong₂ B.await_until_ (~ᵣ-v V ~r) (~ᵣ-lift M ~r)
~ᵣ-m (coerce p q M) ~r = ~ᵣ-m M ~r


-- RELATED SUBSTITUTIONS ACT THE SAME ON RELATED TERMS

~ₛ-v : {Γ Δ : Ctx} {X : VType} (V : Γ ⊢V⦂ X)
       {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
       s ~ₛ s† →
       ------------
       emb-tm-v (V [ s ]v) ≡ (emb-tm-v V) B.[ s† ]v

~ₛ-m : {Γ Δ : Ctx} {X : CType} (M : Γ ⊢M⦂ X)
       {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
       s ~ₛ s† →
       ------------
       emb-tm-m (M [ s ]m) ≡ (emb-tm-m M) B.[ s† ]m

~-lift : {Γ Δ : Ctx} {X : VType}
         {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
         s ~ₛ s† →
         ----------
         lift {X = X} s ~ₛ B.lift s†

~-lift ~s Hd = refl
~-lift {s = s} ~s (Tl x) rewrite sym (~s x) = ~ᵣ-v (s x) (λ {Hd → refl; (Tl x) → refl})

~ₛ-lift : {Γ Δ : Ctx} {X : VType} {Y : CType} (M : Γ ∷ X ⊢M⦂ Y)
          {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
          s ~ₛ s† →
          ------------
          emb-tm-m (M [ lift s ]m) ≡ (emb-tm-m M) B.[ B.lift s† ]m

~ₛ-lift M ~s = ~ₛ-m M (λ {Hd → refl; (Tl x) → trans (~ᵣ-v _ (λ _ → refl)) (cong (B.V-rename B.Tl) (~s x))})

~ₛ-v (` x) ~s = ~s x
~ₛ-v (`` c) ~r = refl
~ₛ-v (ƛ M) ~r = cong B.ƛ (~ₛ-lift M ~r)
~ₛ-v ⟨ V ⟩ ~r = cong B.⟨_⟩ (~ₛ-v V ~r)

~ₛ-m (return V) ~r = cong B.return (~ₛ-v V ~r)
~ₛ-m (let= M `in N) ~r = cong₂ B.let=_`in_ (~ₛ-m M ~r) (~ₛ-lift N ~r)
~ₛ-m (V · W) ~r = cong₂ B._·_ (~ₛ-v V ~r) (~ₛ-v W ~r)
~ₛ-m (↑ op p V M) ~r = cong₂ (B.↑ op) (~ₛ-v V ~r) (~ₛ-m M ~r)
~ₛ-m (↓ op V M) ~r = cong₂ (B.↓ op) (~ₛ-v V ~r) (~ₛ-m M ~r)
~ₛ-m (promise op ∣ p ↦ M `in N) ~r = cong₂ (B.promise op ↦_`in_) (~ₛ-lift M ~r) (~ₛ-lift N ~r)
~ₛ-m (await V until M) ~r = cong₂ B.await_until_ (~ₛ-v V ~r) (~ₛ-lift M ~r)
~ₛ-m (coerce p q M) ~r = ~ₛ-m M ~r


-- FURTHER IDENTITIES ABOUT RELATED RENAMINGS, SUBSTITUTIONS AND TERMS

~ᵣ-wk₁-v : {Γ : Ctx} {X Z : VType}
           (V : Γ ⊢V⦂ X) →
           -----------
           emb-tm-v (V-rename (wk₁ {X = Z}) V) ≡ B.V-rename (B.wk₁) (emb-tm-v V)
             
~ᵣ-wk₁-v V = ~ᵣ-v V (λ _ → refl)

~ᵣ-wk₂-wk₁-m : {Γ : Ctx} {X Z : VType} {Y : CType}
               (M : Γ ∷ X ⊢M⦂ Y) →
               -----------
               emb-tm-m (M-rename (wk₂ (wk₁ {X = Z})) M) ≡ B.M-rename (B.wk₂ B.wk₁) (emb-tm-m M)

~ᵣ-wk₂-wk₁-m M = ~ᵣ-m M (λ {Hd → refl; (Tl x) → refl})

~ₛᵣ-m  : {Γ : Ctx} {X : VType} {Y : CType}
         (M : Γ ∷ X ⊢M⦂ Y) (V : Γ ⊢V⦂ X) →
         -----------
         emb-tm-m (M [ id-subst [ V ]s ]m) ≡ (emb-tm-m M) B.[ B.id-subst B.[ emb-tm-v V ]s ]m

~ₛᵣ-m  M V = ~ₛ-m M (λ {Hd → refl; (Tl x) → refl})

~-strengthen : {Γ : Ctx} {X : VType} {A : BType}
               (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A) →
               -----------------------
               emb-tm-v (strengthen-val {Δ = X ∷ₗ []ₗ} V) ≡ B.strengthen-val {X = emb-ty-v X} (emb-tm-v V)

~-strengthen (` Tl x) = refl
~-strengthen (`` c) = refl


-- SINCE AEFFBASE DOESN'T HAVE COERCION, WE HAVE TO KEEP TRACK OF REDUCTIONS INVOLVING COERCE TERMS
-- USING CONTEXT SHAPES

data ContextShape : Set where
  [-] : ContextShape
  coe other : ContextShape → ContextShape

variable
  CC CC' : ContextShape

infix 4 _↝c_
data _↝c_ : ContextShape → ContextShape → Set where
  coe-[-] : coe [-] ↝c [-]
  coe-↓ : coe (other CC) ↝c other (coe CC)
  coe-ctx : CC ↝c CC' → coe CC ↝c coe CC'
  other-ctx : CC ↝c CC' → other CC ↝c other CC'


-- FINDING THE CONTEXT SHAPE OF A TERM

ctx-shape-of : {Γ : Ctx} {X : CType} → Γ ⊢M⦂ X → ContextShape
ctx-shape-of (return _) = [-]
ctx-shape-of (let= M `in _) = other (ctx-shape-of M)
ctx-shape-of (_ · _) = [-]
ctx-shape-of (↑ _ _ _ M) = other (ctx-shape-of M)
ctx-shape-of (↓ _ _ M) = other (ctx-shape-of M)
ctx-shape-of (promise _ ∣ _ ↦ _ `in N) = other (ctx-shape-of N)
ctx-shape-of (await _ until M) = [-]
ctx-shape-of (coerce _ _ M) = coe (ctx-shape-of M)


-- THE SIMULATION RESULT: A REDUCTION IN AEFF
-- EITHER CORRESPONDS TO A REDUCTION IN AEFFBASE,
-- OR IT IS A REDUCTION OF THE CONTEXT SHAPE

sim : {Γ : Ctx} {X : CType} {M N : Γ ⊢M⦂ X} →
      M ↝↝ N →
      ------------------------
      emb-tm-m M B.↝↝ emb-tm-m N ⊎
      (emb-tm-m M ≡ emb-tm-m N)
        × ctx-shape-of M ↝c ctx-shape-of N

sim (apply M V) rewrite ~ₛᵣ-m M V = inj₁ (B.apply _ _)
sim (let-return V N) rewrite ~ₛᵣ-m N V = inj₁ (B.let-return _ _)
sim (let-↑ p V M N) = inj₁ (B.let-↑ _ _ _)
sim (let-promise {X} p M₁ M₂ N) rewrite ~ᵣ-wk₂-wk₁-m {Z = ⟨ X ⟩} N = inj₁ (B.let-promise _ _ _)
sim (promise-↑ p q V M N) rewrite ~-strengthen V = inj₁ (B.promise-↑ _ _ _)
sim (↓-return V W) = inj₁ (B.↓-return _ _)
sim (↓-↑ p V W M) = inj₁ (B.↓-↑ _ _ _)
sim (↓-promise-op {X} p V M N) rewrite ~ₛᵣ-m M V | ~ᵣ-wk₁-v {Z = ⟨ X ⟩} V = inj₁ (B.↓-promise-op _ _ _)
sim (↓-promise-op' {X} p q V M N) rewrite ~ᵣ-wk₁-v  {Z = ⟨ X ⟩} V = inj₁ (B.↓-promise-op' (λ z → p (sym z)) _ _ _)
sim (await-promise V M) rewrite ~ₛᵣ-m M V = inj₁ (B.await-promise _ _)
sim (context-let r) with sim r
... | inj₁ r = inj₁ (B.context-let r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-↑ r) with sim r
... | inj₁ r = inj₁ (B.context-↑ r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-↓ r) with sim r
... | inj₁ r = inj₁ (B.context-↓ r)
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


-- REDUCTION OF A CONTEXT SHAPE DECREASES ITS HEIGHT
-- SO CONTEXT SHAPE REDUCTION IS WELL-FOUNDED

height : ContextShape → ℕ
height [-] = zero
height (coe CC) = suc (height CC)
height (other CC) = suc (height CC)

∣_∣ : ContextShape → ℕ
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


-- STRONG NORMALISATION PROOF BY MEANS OF THE SIMULATION AND
-- WELL-FOUNDEDNESS OF CONTEXT SHAPE REDUCTION

data SN {Γ : Ctx} {X : CType} (M : Γ ⊢M⦂ X) : Set where
  sn : ({N : Γ ⊢M⦂ X} → M ↝↝ N → SN N) → SN M

sn*→sn : {Γ : Ctx} {X : CType} {M N : Γ ⊢M⦂ X} →
         Acc _<_ ∣ ctx-shape-of M ∣ →
         --------------------------------
         SN* (emb-tm-m M) → M ↝↝ N → SN N

sn*→sn aM sM r with sim r
sn*→sn aM (sn* f) _ | inj₁ r = sn (sn*→sn (<-wellFounded _) (f r))
sn*→sn (acc aM) sM _ | inj₂ (e , r) rewrite e = sn (sn*→sn (aM (size-mono-↝ r)) sM)

{- COROLLARY 19 -}

strong-norm : {Γ : Ctx} {X : CType} (M : Γ ⊢M⦂ X) → SN M
strong-norm M = sn (sn*→sn (<-wellFounded _) (strong-norm* (emb-tm-m M)))