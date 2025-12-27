open import AEffStarSN.AEffStar
open import AEffStarSN.Continuations
open import AEffStarSN.SubstitutionProperties

open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂) renaming (module ≡-Reasoning to Eq)

open Eq using (begin_; step-≡-⟩; _∎)

open import EffectAnnotations using (Σₛ)
open import AEff using (payload)

open import Function.Base using () renaming (_∘_ to _∘f_)

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
  {Γ' : Ctx} {r : Ren Γ Γ'} {W : Γ' ⊢V⦂ X} → VRed W → CRed (V-rename r V · W)
VRed {Γ} {⟨ X ⟩} V =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Y Z : Type} (K : Γ' ⊢K⦂ Y ⊸ Z) (N : Γ' ∷ X ⊢M⦂ Y) → ARed K N → SN' (K aK await V-rename r V until N)

CRed {Γ} {X} M =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Y : Type} (K : Γ' ⊢K⦂ X ⊸ Y) → KRed K → SN' (K aK M-rename r M)

KRed {Γ} {X} K =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → SN' (K-rename r K aK return V)

ARed {Γ} {Y} {Z} {X} K N =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → SN' (K-rename r K aK await ⟨ V ⟩ until M-rename (wk₂ r) N)

ren-id-k : (K : Γ ⊢K⦂ X ⊸ Y) → K-rename idr K ≡ K
ren-id-k id = refl
ren-id-k (K ∘ Tl M) = cong₂ (λ z w → z ∘ Tl w) (ren-id-k K) ⌊ ren-id-l ⌋m
ren-id-k (K ∘ T↓ op V) = cong₂ (λ z w → z ∘ T↓ _ w) (ren-id-k K) ⌊ ren-id ⌋v

ren-ren-k : (K : Γ ⊢K⦂ X ⊸ Y) → K-rename r (K-rename r' K) ≡ K-rename (r ∘f r') K
ren-ren-k id = refl
ren-ren-k (K ∘ Tl M) = cong₂ (λ z w → z ∘ Tl w) (ren-ren-k K) ⌊ ren-ren-l ⌋m
ren-ren-k (K ∘ T↓ op V) = cong₂ (λ z w → z ∘ T↓ _ w) (ren-ren-k K) ⌊ ren-ren ⌋v

vred-r : {V : Γ ⊢V⦂ X} → VRed V → VRed (V-rename r V)
vred-r {X = ``` x} rV = tt
vred-r {X = X ⇒ Y} rV rW K rK = subst SN' (cong (λ z → K aK V-rename _ z · _) (sym ⌊ ren-ren ⌋v)) (rV rW K rK)
vred-r {X = ⟨ X ⟩} rV K N rA = subst SN' (cong (λ z → K aK await z until _) (sym ⌊ ren-ren ⌋v)) (rV K N rA)

kred-r : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → KRed (K-rename r K)
kred-r K rK rV = subst SN' (cong (_aK _) (sym (ren-ren-k K))) (rK rV)

CRedSub' : Γ ∷ X ⊢M⦂ Y → Set
CRedSub' {Γ} {X} M = {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → CRed (M-rename (wk₂ r) M [ ids [ V ]s ]m)

sn-var-await : (K : Γ ⊢K⦂ Y ⊸ Z) → SN' (K aK await ` x until N)
sn-var-await K r with aK→`aK K r
... | `aK K (T-await _ _ _) = sn'→sn (sn-var-await K)

vred-var : (x : X ∈ Γ) → VRed (` x)
vred-var {X = ``` _} _ = tt
vred-var {X = _ ⇒ _} _ _ K _ r with aK→`aK K r
... | `aK _ (context-T _ ())
vred-var {X = ⟨ _ ⟩} _ K _ _ = sn-var-await K

cred-kred : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → CRed M → SN' (K aK M)
cred-kred K rK rM = subst (λ z → SN' (K aK z)) ⌊ ren-id ⌋m (rM K rK)

credsub'→cred : CRedSub' M → CRed (M-rename (wk₂ r) M)
credsub'→cred rM =
  subst CRed
    (trans ⌊ sub-ren (λ {Hd → refl; (Tl x) → refl}) ⌋m (cong (M-rename _) ⌊ sub-id ⌋m))
    (rM (vred-var Hd))

credsub'-r : CRedSub' M → CRedSub' (M-rename (wk₂ r) M)
credsub'-r rM rV K rK = subst (λ z → SN' (K aK M-rename _ (z [ ids [ _ ]s ]m))) (sym ⌊ ren-ren-l ⌋m) (rM rV K rK)

sn-ƛ : (K : Γ ⊢K⦂ X ⊸ Y) → SN (K aK M [ ids [ W ]s ]m) → SN' (K aK ƛ M · W)
sn-ƛ K s r with aK→`aK K r
... | `id (apply _ _) = s
... | `aK _ (context-T _ (apply _ _)) = s

vred-ƛ : CRedSub' M → VRed (ƛ M)
vred-ƛ rM rW K rK = sn-ƛ K (subst (λ z → SN (K aK z [ ids [ _ ]s ]m)) (sym ⌊ ren-ren-l ⌋m) (sn'→sn (cred-kred K rK (rM (vred-r rW)))))

sn-let : (K : Γ ⊢K⦂ X ⊸ Y) → SN (K aK N [ ids [ V ]s ]m) → SN' (K aK let= return V `in N)
sn-let K s r with aK→`aK K r
... | `id (let-return _ _) = s
... | `aK _ (context-T _ (let-return _ _)) = s

kred-let : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → CRedSub' N → KRed (K ∘ Tl N)
kred-let K rK rN rV = sn-let (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rN rV)))

cred-let : CRed M → CRedSub' N → CRed (let= M `in N)
cred-let rM rN K rK = rM (K ∘ Tl _) (kred-let K rK (credsub'-r rN))

sn-↓ : (K : Γ ⊢K⦂ X ⊸ Y) → SN (K aK return V) → SN' (K aK ↓ op W (return V))
sn-↓ K s r with aK→`aK K r
... | `id (↓-return _ _) = s
... | `aK _ (context-T _ (↓-return _ _)) = s

kred-↓ : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → KRed (K ∘ T↓ op V)
kred-↓ K rK rV = sn-↓ (K-rename _ K) (sn'→sn (rK rV))

cred-↓ : CRed M → CRed (↓ op V M)
cred-↓ rM K rK = rM (K ∘ T↓ _ _) (kred-↓ K rK)

sn-↑ : (K : Γ ⊢K⦂ X ⊸ Y) → SN (K aK M) → SN' (K aK (↑ op V M))
sn-↑ K (sn f) r with aK→`aK K r
... | `id (↑-discard _) = sn f
... | `id (context-↑ r) = sn'→sn (sn-↑ id (f r))
... | `aK K (T-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | `aK _ (context-T _ (↑-discard _)) = sn f
... | `aK _ (context-T _ (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))

cred-↑ : CRed M → CRed (↑ op V M)                        
cred-↑ rM K rK = sn-↑ K (sn'→sn (rM K rK))

kred-comm-t : (K : Γ ⊢K⦂ Z ⊸ U) →
              KRed (K ∘ T ∘ Tl N) →
              -------------------
              KRed (K ∘ Tl (T-rename wk₁ T aT N))
kred-comm-t K rK rV =
  sn-let (K-rename _ K)
    (subst (λ z → SN (K-rename _ K aK z aT _))
      eq (rK rV (context-K (K-rename _ K ∘ _) (let-return _ _))))
  where
  eq : T-rename r T
       ≡
       T-rename (wk₂ r) (T-rename wk₁ T) [ ids [ V ]s ]t
  eq {r = r} {T = T} {V = V} = 
    begin
      T-rename r T
    ≡⟨ sym ⌊ eq₁ _ _ ⌋t ⟩
      T-rename wk₁ (T-rename r T) [ ids [ V ]s ]t
    ≡⟨ cong (_[ _ ]t) (trans ⌊ ren-ren ⌋t (sym ⌊ ren-ren ⌋t)) ⟩
      T-rename (wk₂ r) (T-rename wk₁ T) [ ids [ V ]s ]t
    ∎

kred-↝ : (K : Γ ⊢K⦂ Y ⊸ Z) →
         M ↝ N →
         KRed (K ∘ Tl M) →
         ---------------
         KRed (K ∘ Tl N)
kred-↝ K r rK rV =
  sn-let (K-rename _ K)
    (sn→sn'
      (rK rV (context-K (K-rename _ K) (let-return _ _)))
      (context-K (K-rename _ K) (sub-↝ _ (ren-↝ _ r))))

sn-promise : (K : Γ ⊢K⦂ Y ⊸ Z) →
             KRed (K ∘ Tl N) →
             CRedSub' M →
             SN (K-rename wk₁ K aK N) →
             ---------------------------
             SN' (K aK promise op ↦ M `in N)
sn-promise K rK rM (sn h) r with aK→`aK K r
... | `id (promise-↑ V _ _) =
  sn'→sn (sn-↑ id (sn'→sn (sn-promise id (kred-↝ K (↑-discard V) rK) rM (h (↑-discard _)))))
... | `id (context-promise r) =
  sn'→sn (sn-promise id (kred-↝ id r rK) rM (h r))
... | `aK K (T-promise _ _ _) =
  sn'→sn (sn-promise K (kred-comm-t K rK) rM (sn h))
... | `aK K (↓-promise-op _ _ _) =
  sn'→sn (cred-kred (K ∘ Tl _) (kred-comm-t K rK) (subst (λ z → CRed (z [ ids [ _ ]s ]m)) ⌊ ren-id-l ⌋m (rM tt)))
... | `aK _ (context-T _ (promise-↑ V _ _)) =
  sn'→sn (sn-↑ K (sn'→sn (sn-promise K (kred-↝ K (↑-discard V) rK) rM (h (context-K (K-rename wk₁ K) (↑-discard _))))))
... | `aK _ (context-T _ (context-promise r)) =
  sn'→sn (sn-promise K (kred-↝ K r rK) rM (h (context-K (K-rename wk₁ K) r)))

cred-promise : CRedSub' M → CRedSub' N → CRed (promise op ↦ M `in N)
cred-promise rM rN K rK =
  sn-promise K (kred-let K rK (credsub'-r rN)) (credsub'-r rM)
    (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (credsub'→cred rN)))

cred→sn : CRed M → SN' M
cred→sn rM = subst SN' ⌊ ren-id ⌋m (rM id (λ _ ()))

cred-return : VRed V → CRed (return V)
cred-return rV K rK = subst (λ z → SN' (z aK return _)) (ren-id-k K) (rK (vred-r rV))

sn-await : (K : Γ ⊢K⦂ Y ⊸ Z) → SN (K aK N [ ids [ V ]s ]m) → SN' (K aK await ⟨ V ⟩ until N)
sn-await K s r with aK→`aK K r
... | `id (await-promise _ _) = s
... | `aK K (T-await T _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aK (z aT _))) (sym ⌊ eq₁ _ _ ⌋t) s))
... | `aK _ (context-T _ (await-promise _ _)) = s

ared-await : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → CRedSub' N → ARed K N
ared-await K rK rN rV = sn-await (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rN rV)))

cred-await : VRed V → CRedSub' N → CRed (await V until N)
cred-await rV rN K rK = rV K _ (ared-await K rK (credsub'-r rN))

vred-⟨⟩ : VRed V → VRed ⟨ V ⟩
vred-⟨⟩ rV K N rK = subst₂ (λ z w → SN' (z aK await ⟨ V-rename _ _ ⟩ until w)) (ren-id-k K) ⌊ ren-id-l ⌋m (rK (vred-r rV))

SubRed : (s : Sub Γ Γ') → Set
SubRed {Γ} s = {X : Type} (x : X ∈ Γ) → VRed (s x)

VRedSub : Γ ⊢V⦂ X → Set
VRedSub {Γ} V = {Γ' : Ctx} {s : Sub Γ Γ'} → SubRed s → VRed (V [ s ]v)

CRedSub : Γ ⊢M⦂ X → Set
CRedSub {Γ} M = {Γ' : Ctx} {s : Sub Γ Γ'} → SubRed s → CRed (M [ s ]m)

subred-⨟ : SubRed s → SubRed (s ⨟ ren r)
subred-⨟ {r = r} rs x = subst VRed (sym ⌊ ren-rename ⌋v) (vred-r (rs x))

subred-[]s : SubRed s → VRed V → SubRed (s [ V ]s)
subred-[]s rs rV Hd = rV
subred-[]s rs rV (Tl x) = rs x

cred-⨟ : SubRed s → CRedSub M → CRedSub' (M [ lift s ]m)
cred-⨟ rs rM rV K rK = subst (λ z → SN' (K aK M-rename _ z)) eq (rM (subred-[]s (subred-⨟ rs) rV) K rK)
  where
  eq : M [ (s ⨟ ren r) [ V ]s ]m
       ≡
       M-rename (wk₂ r) (M [ lift s ]m) [ ids [ V ]s ]m
  eq {M = M} {s = s} {r = r} {V = V} =
    begin
      M [ (s ⨟ ren r) [ V ]s ]m
    ≡⟨ sym ⌊ eq₂ _ _ ⌋m ⟩
      M [ lift (s ⨟ ren r) ]m [ ids [ V ]s ]m
    ≡⟨ cong (_[ ids [ V ]s ]m) ⌊ cong-sub (λ x → trans (sym (lift-⨟ x)) ⌊ cong-sub {TT = ⊢V (lift s x)} (λ {Hd → refl; (Tl x) → refl}) ⌋v) ⌋m ⟩
      M [ lift s ⨟ ren (wk₂ r) ]m [ ids [ V ]s ]m
    ≡⟨ cong (_[ ids [ V ]s ]m) (sym ⌊ sub-sub ⌋m) ⟩
      M [ lift s ]m [ ren (wk₂ r) ]m [ ids [ V ]s ]m
    ≡⟨ cong (_[ ids [ V ]s ]m) ⌊ ren-rename ⌋m ⟩
      M-rename (wk₂ r) (M [ lift s ]m) [ ids [ V ]s ]m
    ∎

fund-v : (V : Γ ⊢V⦂ X) → VRedSub V

fund-m : (M : Γ ⊢M⦂ X) → CRedSub M

fund-v (` x) rs = rs x
fund-v (`` c) rs = tt
fund-v (ƛ M) rs = vred-ƛ (cred-⨟ rs (fund-m M))
fund-v ⟨ V ⟩ rs = vred-⟨⟩ (fund-v V rs)

fund-m (return V) rs = cred-return (fund-v V rs)
fund-m (V · W) rs = subst (λ z → CRed (z · _)) ⌊ ren-id ⌋v (fund-v V rs (fund-v W rs))
fund-m (↑ op V M) rs = cred-↑ (fund-m M rs)
fund-m (promise op ↦ M `in N) rs = cred-promise (cred-⨟ rs (fund-m M)) (cred-⨟ rs (fund-m N))
fund-m (await V until M) rs = cred-await (fund-v V rs) (cred-⨟ rs (fund-m M))
fund-m (let= M `in N) rs = cred-let (fund-m M rs) (cred-⨟ rs (fund-m N))
fund-m (↓ op V M) rs = cred-↓ (fund-m M rs)

all-terms-red : (M : Γ ⊢M⦂ X) → CRed M
all-terms-red M rewrite sym ⌊ sub-id {TT = ⊢M M} ⌋m = fund-m M vred-var

strong-norm : (M : Γ ⊢M⦂ X) → SN M
strong-norm M = sn'→sn (cred→sn (all-terms-red M))