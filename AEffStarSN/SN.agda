open import AEffStarSN.AEffStar
open import AEffStarSN.Continuations
open import AEffStarSN.SubstitutionProperties using (sub-↝; sub-id; eq₁; eq₂; ⊢M; ⊢T; ⌊_⌋v; ⌊_⌋m; ⌊_⌋t)

open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (subst; sym)

open import EffectAnnotations using (Σₛ)
open import AEff using (payload)

module AEffStarSN.SN where

data SN (M : Γ ⊢M⦂ X) : Set where
  sn : ({N : Γ ⊢M⦂ X} → M ↝ N → SN N) → SN M

SN' : (M : Γ ⊢M⦂ X) → Set
SN' {Γ} {X} M = {N : Γ ⊢M⦂ X} → M ↝ N → SN N

sn'→sn : SN' M → SN M
sn'→sn s = sn s

sn→sn' : SN M → SN' M
sn→sn' (sn f) = f

VRed : Γ ⊢V⦂ X → Set

CRed : Γ ⊢M⦂ X → Set

KRed : Γ ⊢K⦂ X ⊸ Y → Set

ARed : Γ ⊢K⦂ Y ⊸ Z → Γ ∷ X ⊢M⦂ Y → Set

VRed {Γ} {``` _} V =
  ⊤
VRed {Γ} {X ⇒ Y} V =
  {W : Γ ⊢V⦂ X} → VRed W → CRed (V · W)
VRed {Γ} {⟨ X ⟩} V =
  {Y Z : Type} (K : Γ ⊢K⦂ Y ⊸ Z) (N : Γ ∷ X ⊢M⦂ Y) → ARed K N → SN' (K aK (await V until N))

CRed {Γ} {X} M =
  {Y : Type} (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → SN' (K aK M)

KRed {Γ} {X} id =
  ⊤
KRed {Γ} {X} (K ∘ Tl N) =
  {V : Γ ⊢V⦂ X} → VRed V → SN' (K aK N [ ids [ V ]s ]m)
KRed {Γ} {X} (K ∘ T↓ op V) =
  KRed K
KRed {Γ} {X} (K ∘ Tc) =
  KRed K

ARed {Γ} {Y} {Z} {X} K N =
  {V : Γ ⊢V⦂ X} → VRed V → SN' (K aK (await ⟨ V ⟩ until N))

CRedSub : Γ ∷ X ⊢M⦂ Y → Set
CRedSub {Γ} {X} M = {V : Γ ⊢V⦂ X} → VRed V → CRed (M [ ids [ V ]s ]m)

vred-ƛ  : {M : Γ ∷ X ⊢M⦂ Y} → CRedSub M → VRed (ƛ M)
vred-ƛ f rV K rK r with aK→`aK K r
... | `id (apply _ _) = sn'→sn (f rV K rK)
... | `aK _ (context-T _ (apply _ _)) = sn'→sn (f rV K rK)

cred→sn : CRed M → SN' M
cred→sn rM = rM id tt

sn-★-await : {N : Γ ∷ X ⊢M⦂ Y}
             (K : Γ ⊢K⦂ Y ⊸ Z) →
             ----------------
             SN' (K aK (await ★ until N))
sn-★-await K r with aK→`aK K r
... | `aK K (T-await _ _ _) = sn'→sn (sn-★-await K)

vred-★ : VRed {Γ} {⟨ X ⟩} ★
vred-★ K _ _ = sn-★-await K

cred-let : {N : Γ ∷ X ⊢M⦂ Y} → CRed M → CRedSub N → CRed (let= M `in N)
cred-let rM rN K rK = rM (K ∘ Tl _) (λ rV → rN rV K rK)

cred-↓ : CRed M → CRed (↓ op Vᵒᵖ M)
cred-↓ rM K = rM (K ∘ T↓ _ _)

cred-coerce : CRed M → CRed (coerce M)
cred-coerce rM K = rM (K ∘ Tc)

cred-return : VRed V → CRed (return V)
cred-return rV K rK r with aK→`aK K r
... | `aK _ (let-return _ _) = sn'→sn (rK rV)
... | `aK K (↓-return _ _) = sn'→sn (cred-return rV K rK)
... | `aK K (coerce-return _) = sn'→sn (cred-return rV K rK)

sn-↑ : (K : Γ ⊢K⦂ X ⊸ Y) →
       SN (K aK M) →
       --------------
       SN' (K aK (↑ op Vᵒᵖ M))
sn-↑ K (sn f) r with aK→`aK K r
... | `id (↑-discard _) = sn f
... | `id (context-↑ r) = sn'→sn (sn-↑ id (f r))
... | `aK K (T-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | `aK _ (context-T _ (↑-discard _)) = sn f
... | `aK _ (context-T _ (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))

kred-comm-t : {T : Γ ⊢T⦂ Y ⊸ Z} {N : Γ ∷ X ⊢M⦂ Y}
              (K : Γ ⊢K⦂ Z ⊸ U) →
              KRed (K ∘ T ∘ Tl N) →
              -------------------
              KRed (K ∘ Tl (T-rename wk₁ T aT N))
kred-comm-t {T = T} K rK {V} rewrite ⌊ eq₁ (⊢T T) V ⌋t = rK

kred-↝ : {M N : Γ ∷ X ⊢M⦂ Y} →
         M ↝ N →
         (K : Γ ⊢K⦂ Y ⊸ Z) →
         KRed (K ∘ Tl M) →
         ---------------
         KRed (K ∘ Tl N)
kred-↝ r K rK rV = sn→sn' (rK rV (context-K K (sub-↝ _ r)))

sn-promise : {M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩}
             {N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y}
             (K : Γ ⊢K⦂ Y ⊸ Z) →
             KRed (K ∘ Tl N) →
             CRedSub M →
             SN (K aK N [ ids [ ★ ]s ]m) →
             ---------------------------
             SN' (K aK (promise op ↦ M `in N))
sn-promise K rK rM (sn h) r with aK→`aK K r
... | `id (promise-↑ V _ _) =
  sn'→sn (sn-↑ id (sn'→sn (sn-promise id (kred-↝ (↑-discard V) id rK) rM (h (↑-discard _)))))
... | `id (context-promise r) =
  sn'→sn (sn-promise id (kred-↝ r id rK) rM (h (sub-↝ _ r)))
... | `aK K (T-promise _ _ _) =
  sn'→sn (sn-promise K (kred-comm-t K rK) rM (sn'→sn (kred-comm-t K rK vred-★)))
... | `aK K (↓-promise-op _ _ _) =
  sn'→sn (cred-coerce (rM tt) (K ∘ Tl _) (kred-comm-t K rK))
... | `aK _ (context-T _ (promise-↑ V _ _)) =
  sn'→sn (sn-↑ K (sn'→sn (sn-promise K (kred-↝ (↑-discard V) K rK) rM (h (context-K K (↑-discard _))))))
... | `aK _ (context-T _ (context-promise r)) =
  sn'→sn (sn-promise K (kred-↝ r K rK) rM (h (context-K K (sub-↝ _ r))))

sn-await : {N : Γ ∷ X ⊢M⦂ Y} →
           (K : Γ ⊢K⦂ Y ⊸ Z) →
           SN (K aK N [ ids [ V ]s ]m) →
           -----------------------
           SN' (K aK (await ⟨ V ⟩ until N))
sn-await K s r with aK→`aK K r
... | `id (await-promise _ _) = s
... | `aK K (T-await T _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aK (z aT _))) (sym ⌊ eq₁ _ _ ⌋t) s))
... | `aK _ (context-T _ (await-promise _ _)) = s

cred-↑ : CRed M → CRed (↑ op Vᵒᵖ M)                        
cred-↑ rM K rK = sn-↑ K (sn'→sn (rM K rK))

cred-promise : {M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩}
               {N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y} →
               CRedSub N →
               CRedSub M →
               ---------
               CRed (promise op ↦ M `in N)
cred-promise rN rM K rK = sn-promise K (λ rV → rN rV K rK) rM (sn'→sn (rN vred-★ K rK))

cred-await : {V : Γ ⊢V⦂ ⟨ X ⟩} {N : Γ ∷ X ⊢M⦂ Y} →
             VRed V →
             CRedSub N →
             ---------
             CRed (await V until N)
cred-await rV rN K rK = rV K _ (λ rW → sn-await K (sn'→sn (rN rW K rK)))

SubRed : (s : Sub Γ Γ') → Set
SubRed {Γ} s = {X : Type} (x : X ∈ Γ) → VRed (s x)

cred-⨟ : {N : Γ ∷ X ⊢M⦂ Y} →
         SubRed s →
         ({Γ'' : Ctx} {s' : Sub (Γ ∷ X) Γ''} → SubRed s' → CRed (N [ s' ]m)) →
         -------------------------
         CRedSub (N [ lift s ]m)
cred-⨟ {s = s} {N = N} rs f {V} rV
  rewrite ⌊ eq₂ {s = s} (⊢M N) V ⌋m =
  f (λ {Hd → rV; (Tl x) → rs x})

fund-v : (V : Γ ⊢V⦂ X) → SubRed s → VRed (V [ s ]v)

fund-m : (M : Γ ⊢M⦂ X) → SubRed s → CRed (M [ s ]m)

fund-v (` x) rs =
  rs x
fund-v (`` c) rs =
  tt
fund-v (ƛ M) rs =
  vred-ƛ (cred-⨟ rs (fund-m M))
fund-v ⟨ V ⟩ rs K _ rA =
  rA (fund-v V rs)
fund-v ★ rs =
  vred-★

fund-m (return V) rs =
  cred-return (fund-v V rs)
fund-m (V · W) rs =
  fund-v V rs (fund-v W rs)
fund-m (let= M `in N) rs =
  cred-let (fund-m M rs) (cred-⨟ rs (fund-m N))
fund-m (↑ op V M) rs =
  cred-↑ (fund-m M rs)
fund-m (↓ op V M) rs =
  cred-↓ (fund-m M rs)
fund-m (promise op ↦ M `in N) rs =
  cred-promise (cred-⨟ rs (fund-m N)) (cred-⨟ rs (fund-m M))
fund-m (await V until M) rs =
  cred-await (fund-v V rs) (cred-⨟ rs (fund-m M))
fund-m (coerce M) rs =
  cred-coerce (fund-m M rs)

sn-var-await : {N : Γ ∷ X ⊢M⦂ Y}
               {x : ⟨ X ⟩ ∈ Γ}
               (K : Γ ⊢K⦂ Y ⊸ Z) →
               ----------------
               SN' (K aK (await ` x until N))
sn-var-await K r with aK→`aK K r
... | `aK K (T-await _ _ _) = sn'→sn (sn-var-await K)

vred-var : (x : X ∈ Γ) → VRed (` x)
vred-var {X = ``` c} x = tt
vred-var {X = X ⇒ Y} x rV K rK r with aK→`aK K r
... | `aK _ (context-T _ ())
vred-var {X = ⟨ X ⟩} x K _ rA = sn-var-await K

all-terms-red : (M : Γ ⊢M⦂ X) → CRed M
all-terms-red M rewrite sym ⌊ sub-id {T = ⊢M M} ⌋m = fund-m M vred-var

strong-norm : (M : Γ ⊢M⦂ X) → SN M
strong-norm M = sn'→sn (cred→sn (all-terms-red M))