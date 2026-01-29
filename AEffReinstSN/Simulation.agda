{-# OPTIONS --guardedness #-}

open import Data.Nat using (_<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.List using () renaming ([] to []ₗ; _∷_ to _∷ₗ_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Induction.WellFounded using (Acc; acc)

open import AEffReinstSN.Types
open import AEffReinstSN.AEff
open import AEffReinstSN.Preservation
open import AEffReinstSN.Finality
open import AEffReinstSN.Renamings
open import AEffReinstSN.Substitutions
open import AEffReinstSN.CoinductiveEffectAnnotations

open import AEffReinstSN.AEffReinstBaseSN.StronglyNormalising using () renaming (SN to SN*; sn to sn*)
open import AEffReinstSN.AEffReinstBaseSN.Main using () renaming (strong-norm to strong-norm*)
open import AEff.Simulation using (ContextShape; [-]; coe; other; _↝c_; coe-ctx; other-ctx; coe-[-]; coe-↓; ∣_∣; size-mono-↝)
open import AEff.Types using (GType)

import AEffReinstSN.AEffReinstBaseSN.AEff as B

module AEffReinstSN.Simulation where

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
cong₃ f refl refl refl = refl

-- EMBEDDING OF AEFF TYPES, CONTEXTS, VARIABLES AND TERMS INTO AEFFBASE

emb-ty-v : VType → B.Type

emb-ty-c : CType → B.Type

emb-ty-v (``` x) = B.``` x
emb-ty-v (X ⇒ Y) = emb-ty-v X B.⇒ emb-ty-c Y
emb-ty-v (X + Y) = emb-ty-v X B.+ emb-ty-v Y
emb-ty-v ⟨ V ⟩ = B.⟨ emb-ty-v V ⟩
emb-ty-v 𝟙 = B.𝟙

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
emb-tm-v (inl V) = B.inl (emb-tm-v V)
emb-tm-v (inr V) = B.inr (emb-tm-v V)
emb-tm-v ⟨ V ⟩ = B.⟨ emb-tm-v V ⟩
emb-tm-v ★ = B.★

emb-tm-m (return V) = B.return (emb-tm-v V)
emb-tm-m (let= M `in N) = B.let= emb-tm-m M `in emb-tm-m N
emb-tm-m (V · W) = emb-tm-v V B.· emb-tm-v W
emb-tm-m (↑ op p V M) = B.↑ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (↓ op V M) = B.↓ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (promise op ∣ p , q ↦ M `in N) = B.promise op ↦ emb-tm-m M `in emb-tm-m N
emb-tm-m (await V until M) = B.await emb-tm-v V until emb-tm-m M
emb-tm-m (match+ V M N) = B.match+ (emb-tm-v V) (emb-tm-m M) (emb-tm-m N)
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
~ᵣ-v (inl V) ~r = cong B.inl (~ᵣ-v V ~r)
~ᵣ-v (inr V) ~r = cong B.inr (~ᵣ-v V ~r)
~ᵣ-v ⟨ V ⟩ ~r = cong B.⟨_⟩ (~ᵣ-v V ~r)
~ᵣ-v ★ ~r = refl

~ᵣ-m (return V) ~r = cong B.return (~ᵣ-v V ~r)
~ᵣ-m (let= M `in N) ~r = cong₂ B.let=_`in_ (~ᵣ-m M ~r) (~ᵣ-lift N ~r)
~ᵣ-m (V · W) ~r = cong₂ B._·_ (~ᵣ-v V ~r) (~ᵣ-v W ~r)
~ᵣ-m (↑ op p V M) ~r = cong₂ (B.↑ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (↓ op V M) ~r = cong₂ (B.↓ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (promise op ∣ p , q ↦ M `in N) ~r = cong₂ (B.promise op ↦_`in_) (~ᵣ-lift M ~r) (~ᵣ-lift N ~r)
~ᵣ-m (await V until M) ~r = cong₂ B.await_until_ (~ᵣ-v V ~r) (~ᵣ-lift M ~r)
~ᵣ-m (match+ V M N) ~r = cong₃ B.match+ (~ᵣ-v V ~r) (~ᵣ-lift M ~r) (~ᵣ-lift N ~r)
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
~ₛ-v (`` c) ~s = refl
~ₛ-v (ƛ M) ~s = cong B.ƛ (~ₛ-lift M ~s)
~ₛ-v (inl V) ~s = cong B.inl (~ₛ-v V ~s)
~ₛ-v (inr V) ~s = cong B.inr (~ₛ-v V ~s)
~ₛ-v ⟨ V ⟩ ~s = cong B.⟨_⟩ (~ₛ-v V ~s)
~ₛ-v ★ ~s = refl

~ₛ-m (return V) ~s = cong B.return (~ₛ-v V ~s)
~ₛ-m (let= M `in N) ~s = cong₂ B.let=_`in_ (~ₛ-m M ~s) (~ₛ-lift N ~s)
~ₛ-m (V · W) ~s = cong₂ B._·_ (~ₛ-v V ~s) (~ₛ-v W ~s)
~ₛ-m (↑ op p V M) ~s = cong₂ (B.↑ op) (~ₛ-v V ~s) (~ₛ-m M ~s)
~ₛ-m (↓ op V M) ~s = cong₂ (B.↓ op) (~ₛ-v V ~s) (~ₛ-m M ~s)
~ₛ-m (promise op ∣ p , q ↦ M `in N) ~s = cong₂ (B.promise op ↦_`in_) (~ₛ-lift M ~s) (~ₛ-lift N ~s)
~ₛ-m (await V until M) ~s = cong₂ B.await_until_ (~ₛ-v V ~s) (~ₛ-lift M ~s)
~ₛ-m (match+ V M N) ~s = cong₃ B.match+ (~ₛ-v V ~s) (~ₛ-lift M ~s) (~ₛ-lift N ~s)
~ₛ-m (coerce p q M) ~s = ~ₛ-m M ~s


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


-- FINDING THE CONTEXT SHAPE OF A TERM

ctx-shape-of : {Γ : Ctx} {X : CType} → Γ ⊢M⦂ X → ContextShape
ctx-shape-of (return _) = [-]
ctx-shape-of (let= M `in _) = other (ctx-shape-of M)
ctx-shape-of (_ · _) = [-]
ctx-shape-of (↑ _ _ _ M) = other (ctx-shape-of M)
ctx-shape-of (↓ _ _ M) = other (ctx-shape-of M)
ctx-shape-of (promise _ ∣ _ , _ ↦ _ `in N) = other (ctx-shape-of N)
ctx-shape-of (await _ until M) = [-]
ctx-shape-of (match+ _ _ _) = [-]
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
sim (let-promise {X} p q M₁ M₂ N) rewrite ~ᵣ-wk₂-wk₁-m {Z = ⟨ X ⟩} N = inj₁ (B.let-promise _ _ _)
sim (promise-↑ p q r V M N) rewrite ~-strengthen V = inj₁ (B.promise-↑ _ _ _)
sim (↓-return V W) = inj₁ (B.↓-return _ _)
sim (↓-↑ p V W M) = inj₁ (B.↓-↑ _ _ _)
sim (↓-promise-op {X} p q V M N)
  rewrite ~ₛᵣ-m M V |
  ~ᵣ-wk₁-v {Z = ⟨ X ⟩} V |
  ~ᵣ-wk₂-wk₁-m {Z = 𝟙} (M-rename (wk₂ (wk₁ {X = ⟨ X ⟩ + 𝟙})) M) |
  ~ᵣ-wk₂-wk₁-m {Z = ⟨ X ⟩ + 𝟙} M =
  inj₁ (B.↓-promise-op _ _ _)
sim (↓-promise-op' {X} p q r V M N) rewrite ~ᵣ-wk₁-v  {Z = ⟨ X ⟩} V = inj₁ (B.↓-promise-op' (λ z → p (sym z)) _ _ _)
sim (await-promise V M) rewrite ~ₛᵣ-m M V = inj₁ (B.await-promise _ _)
sim (match+-inl V M N) rewrite ~ₛᵣ-m M V = inj₁ (B.match+-inl _ _ _)
sim (match+-inr V M N) rewrite ~ₛᵣ-m N V = inj₁ (B.match+-inr _ _ _)
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
sim (coerce-promise p r M N) = inj₂ (refl , coe-↓)


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

strong-norm : {Γ : Ctx} {X : CType} (M : Γ ⊢M⦂ X) → SN M
strong-norm M = sn (sn*→sn (<-wellFounded _) (strong-norm* (emb-tm-m M)))