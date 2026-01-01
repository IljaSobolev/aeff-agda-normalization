open import AEffStarSN.AEffStar
open import AEffStarSN.StronglyNormalising
open import AEffStarSN.SubstitutionProperties
open import AEffStarSN.Continuations

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (Σ-syntax; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂) renaming (module ≡-Reasoning to Eq)
open Eq using (begin_; step-≡-⟩; _∎)

open import EffectAnnotations using (Σₛ)
open import AEff using (payload)

module AEffStarSN.Main where

VRed : Γ ⊢V⦂ X → Set

CRed : Γ ⊢M⦂ X → Set

KRed : Γ ⊢K⦂ X ⊸ Y → Set

ARed : Γ ⊢K⦂ Y ⊸ Z → Γ ∷ X ⊢M⦂ Y → Set

VRed {Γ} {``` _} V =
  ⊤
VRed {Γ} {X ⇒ Y} V =
  {Γ' : Ctx} {r : Ren Γ Γ'} {W : Γ' ⊢V⦂ X} → VRed W → CRed (V-rename r V · W)
VRed {Γ} {⟨ X ⟩} V =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Y Z : Type} (K : Γ' ⊢K⦂ Y ⊸ Z) (N : Γ' ∷ X ⊢M⦂ Y) → ARed K N → SN' (K aₖ await V-rename r V until N)

CRed {Γ} {X} M =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Y : Type} (K : Γ' ⊢K⦂ X ⊸ Y) → KRed K → SN' (K aₖ M-rename r M)

KRed {Γ} {X} K =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → SN' (K-rename r K aₖ return V)

ARed {Γ} {Y} {Z} {X} K N =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → SN' (K-rename r K aₖ await ⟨ V ⟩ until M-rename (wk₂ r) N)

CRedSub' : Γ ∷ X ⊢M⦂ Y → Set
CRedSub' {Γ} {X} M =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → CRed (M-rename (wk₂ r) M [ ids [ V ]s ]m)

vred-r : VRed V → VRed (V-rename r V)
vred-r {_} {``` x} rV = tt
vred-r {_} {X ⇒ Y} rV rW K rK = subst SN' (cong (λ z → K aₖ V-rename _ z · _) (sym ren-ren-v)) (rV rW K rK)
vred-r {_} {⟨ X ⟩} rV K N rA = subst SN' (cong (λ z → K aₖ await z until _) (sym ren-ren-v)) (rV K N rA)

kred-r : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → KRed (K-rename r K)
kred-r K rK rV = subst SN' (cong (_aₖ _) (sym (ren-ren-k K))) (rK rV)

sn-var-await : {x : ⟨ X ⟩ ∈ Γ} (K : Γ ⊢K⦂ Y ⊸ Z) → SN' (K aₖ await ` x until N)
sn-var-await K r with aₖ→`aₖ K r
... | ↝∘l K (let-await _ _ _) = sn'→sn (sn-var-await K)
... | ↝∘↓ K (↓-await _ _ _) = sn'→sn (sn-var-await K)

vred-var : (x : X ∈ Γ) → VRed (` x)
vred-var {``` _} _ = tt
vred-var {_ ⇒ _} _ _ K _ r with aₖ→`aₖ K r
... | ↝∘l _ (context-let ())
... | ↝∘↓ _ (context-↓ ())
vred-var {⟨ _ ⟩} _ K _ _ = sn-var-await K

cred-kred : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → CRed M → SN' (K aₖ M)
cred-kred K rK rM = subst (λ z → SN' (K aₖ z)) ren-id-m (rM K rK)

credsub'→cred : CRedSub' M → CRed (M-rename (wk₂ r) M)
credsub'→cred rM =
  subst CRed
    (trans (sub-ren-m (λ {Hd → refl; (Tl x) → refl})) (cong (M-rename _) sub-id-m))
    (rM (vred-var Hd))

credsub'-r : CRedSub' M → CRedSub' (M-rename (wk₂ r) M)
credsub'-r rM rV K rK = subst (λ z → SN' (K aₖ M-rename _ (z [ ids [ _ ]s ]m))) (sym ren-ren-l) (rM rV K rK)

sn-ƛ : (K : Γ ⊢K⦂ X ⊸ Y) → SN (K aₖ M [ ids [ W ]s ]m) → SN' (K aₖ ƛ M · W)
sn-ƛ K s r with aₖ→`aₖ K r
... | ↝id (apply _ _) = s
... | ↝∘l _ (context-let (apply _ _)) = s
... | ↝∘↓ _ (context-↓ (apply _ _)) = s

vred-ƛ : CRedSub' M → VRed (ƛ M)
vred-ƛ rM rW K rK = sn-ƛ K (subst (λ z → SN (K aₖ z [ ids [ _ ]s ]m)) (sym ren-ren-l) (sn'→sn (cred-kred K rK (rM (vred-r rW)))))

sn-let : (K : Γ ⊢K⦂ X ⊸ Y) → SN (K aₖ N [ ids [ V ]s ]m) → SN' (K aₖ let= return V `in N)
sn-let K s r with aₖ→`aₖ K r
... | ↝id (let-return _ _) = s
... | ↝∘l _ (context-let (let-return _ _)) = s
... | ↝∘↓ _ (context-↓ (let-return _ _)) = s

kred-let : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → CRedSub' N → KRed (K ∘l N)
kred-let K rK rN rV = sn-let (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rN rV)))

cred-let : CRed M → CRedSub' N → CRed (let= M `in N)
cred-let rM rN K rK = rM (K ∘l _) (kred-let K rK (credsub'-r rN))

sn-↓ : (K : Γ ⊢K⦂ X ⊸ Y) → SN (K aₖ return V) → SN' (K aₖ ↓ op W (return V))
sn-↓ K s r with aₖ→`aₖ K r
... | ↝id (↓-return _ _) = s
... | ↝∘l _ (context-let (↓-return _ _)) = s
... | ↝∘↓ _ (context-↓ (↓-return _ _)) = s

kred-↓ : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → KRed (K ∘↓ op [ V ])
kred-↓ K rK rV = sn-↓ (K-rename _ K) (sn'→sn (rK rV))

cred-↓ : CRed M → CRed (↓ op V M)
cred-↓ rM K rK = rM (K ∘↓ _ [ _ ]) (kred-↓ K rK)

sn-↑ : (K : Γ ⊢K⦂ X ⊸ Y) → SN (K aₖ M) → SN' (K aₖ ↑ op V M)
sn-↑ K (sn f) r with aₖ→`aₖ K r
... | ↝id (context-↑ r) = sn'→sn (sn-↑ id (f r))
... | ↝∘l K (let-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | ↝∘l _ (context-let (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))
... | ↝∘↓ K (↓-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | ↝∘↓ _ (context-↓ (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))

cred-↑ : CRed M → CRed (↑ op V M)
cred-↑ rM K rK = sn-↑ K (sn'→sn (rM K rK))

kred-comm-let : (K : Γ ⊢K⦂ Z ⊸ U) →
                KRed (K ∘l L ∘l N) →
                ---------------------------------------------
                KRed (K ∘l (let= N `in M-rename (wk₂ wk₁) L))
kred-comm-let K rK rV =
  sn-let (K-rename _ K)
    (subst (λ z → SN (K-rename _ K aₖ let= _ `in z))
      eq (rK rV (context-K (K-rename _ K ∘l _) (let-return _ _))))
  where
  eq : M-rename (wk₂ r) L
       ≡
       M-rename (wk₂ (wk₂ r)) (M-rename (wk₂ wk₁) L) [ lift (ids [ V ]s) ]m
  eq {r = r} {L = L} {V = V} = 
    begin
      M-rename (wk₂ r) L
    ≡⟨ wk₂wk₁M[liftids[W]] _ _ ⟩
      M-rename (wk₂ wk₁) (M-rename (wk₂ r) L) [ lift (ids [ V ]s) ]m
    ≡⟨ cong (_[ _ ]m) (trans ren-ren-l (sym ren-ren-l)) ⟩
      M-rename (wk₂ (wk₂ r)) (M-rename (wk₂ wk₁) L) [ lift (ids [ V ]s) ]m
    ∎

kred-comm-↓ : (K : Γ ⊢K⦂ Z ⊸ U) →
              KRed (K ∘↓ op [ V ] ∘l N) →
              ----------------------
              KRed (K ∘l ↓ op (V-rename wk₁ V) N)
kred-comm-↓ K rK rV =
  sn-let (K-rename _ K)
    (subst (λ z → SN (K-rename _ K aₖ ↓ _ z _))
      eq (rK rV (context-K (K-rename _ K ∘↓ _ [ _ ]) (let-return _ _))))
  where
  eq : V-rename r W
       ≡
       V-rename (wk₂ r) (V-rename wk₁ W) [ ids [ V ]s ]v
  eq {r = r} {W = W} {V = V} = 
    begin
      V-rename r W
    ≡⟨ wk₁V[ids[W]] _ _ ⟩
      V-rename wk₁ (V-rename r W) [ ids [ V ]s ]v
    ≡⟨ cong (_[ ids [ V ]s ]v) (trans (ren-ren-v {V = W}) (sym ren-ren-v)) ⟩
      V-rename (wk₂ r) (V-rename wk₁ W) [ ids [ V ]s ]v
    ∎

kred-↝ : (K : Γ ⊢K⦂ Y ⊸ Z) →
         M ↝ N →
         KRed (K ∘l M) →
         --------------
         KRed (K ∘l N)
kred-↝ K r rK rV =
  sn-let (K-rename _ K)
    (sn→sn'
      (rK rV (context-K (K-rename _ K) (let-return _ _)))
      (context-K (K-rename _ K) (sub-↝ _ (ren-↝ _ r))))

sn-↑-e : SN (↑ op V M) → SN M
sn-↑-e (sn sM) = sn (λ r → sn-↑-e (sM (context-↑ r)))

sn-k-↑-e : (K : Γ ⊢K⦂ Y ⊸ Z) → SN (K aₖ ↑ op V M) → SN' (K aₖ M)
sn-k-↑-e K (sn sM) r with aₖ→`aₖ K r
... | ↝id r = sn'→sn (sn-k-↑-e id (sM (context-↑ r)))
... | ↝∘l K r = sn-k-↑-e K (sM (context-K K (let-↑ _ _ _))) (context-K K r)
... | ↝∘↓ K r = sn-k-↑-e K (sM (context-K K (↓-↑ _ _ _))) (context-K K r)

sn↑-↑-e : SN↑ (↑ op V M) (suc n) → SN↑ M n
sn↑-↑-e (sn sM (s≤s le)) = sn (λ r → sn↑-↑-e (sM (context-↑ r))) le

sn↑-k-↑-suc : (K : Γ ⊢K⦂ Y ⊸ Z) → SN↑ (K aₖ ↑ op V M) n → Σ[ m ∈ ℕ ] n ≡ suc m
sn↑-k-↑-suc id (sn sM (s≤s le)) = _ , refl
sn↑-k-↑-suc (K ∘l _) (sn sM _) = sn↑-k-↑-suc K (sM (context-K K (let-↑ _ _ _)))
sn↑-k-↑-suc (K ∘↓ _ [ _ ]) (sn sM _) = sn↑-k-↑-suc K (sM (context-K K (↓-↑ _ _ _)))

sn↑-k-↑-e : (K : Γ ⊢K⦂ Y ⊸ Z) → SN↑ (K aₖ ↑ op V M) (suc n) → ∀ {N} → K aₖ M ↝ N → SN↑ N n
sn↑-k-↑-e K (sn sM le) r with aₖ→`aₖ K r
... | ↝id r with sn sM (s≤s le) ← sM (context-↑ r) = sn (sn↑-k-↑-e id (sn sM (s≤s le))) le
... | ↝∘l K r = sn↑-k-↑-e K (sM (context-K K (let-↑ _ _ _))) (context-K K r)
... | ↝∘↓ K r = sn↑-k-↑-e K (sM (context-K K (↓-↑ _ _ _))) (context-K K r)

kred-↑ : (K : Γ ⊢K⦂ Y ⊸ Z) →
         KRed (K ∘l ↑ op V M) →
         -------------
         KRed (K ∘l M)
kred-↑ K rK rV =
  sn-let (K-rename _ K)
    (sn'→sn (sn-k-↑-e (K-rename _ K) (rK rV (context-K (K-rename _ K) (let-return _ _)))))

k-#↑-let : (K : Γ ⊢K⦂ Y ⊸ Z) → #↑ (K aₖ let= N `in L) ≡ 0

k-#↑-↓ : (K : Γ ⊢K⦂ Y ⊸ Z) → #↑ (K aₖ ↓ op V N) ≡ 0

k-#↑-let id = refl
k-#↑-let (K ∘l _) = k-#↑-let K
k-#↑-let (K ∘↓ _ [ _ ]) = k-#↑-↓ K

k-#↑-↓ id = refl
k-#↑-↓ (K ∘l _) = k-#↑-let K
k-#↑-↓ (K ∘↓ _ [ _ ]) = k-#↑-↓ K

sn-promise : (K : Γ ⊢K⦂ Y ⊸ Z) →
             KRed (K ∘l N) →
             CRedSub' M →
             SN↑ (K-rename wk₁ K aₖ N) n →
             ---------------------------
             SN' (K aₖ promise op ↦ M `in N)
sn-promise K rK rM (sn h le) r with aₖ→`aₖ K r
... | ↝id (promise-↑ _ _ _) with s≤s le ← le =
  sn'→sn (sn-↑ id (sn'→sn (sn-promise id (kred-↑ id rK) rM (sn↑-↑-e (sn h (s≤s le))))))
... | ↝id (context-promise r) =
  sn'→sn (sn-promise id (kred-↝ id r rK) rM (h r))
... | ↝∘l K (let-promise _ _ _) =
  sn'→sn (sn-promise K (kred-comm-let K rK) rM (sn h le))
... | ↝∘↓ K (↓-promise-op _ _ _) =
  sn'→sn (cred-kred (K ∘l _) (kred-comm-↓ K rK) (subst (λ z → CRed (z [ ids [ _ ]s ]m)) ren-id-l (rM tt)))
... | ↝∘↓ K (↓-promise-op' _ _ _ _) =
  sn'→sn (sn-promise K (kred-comm-↓ K rK) rM (sn h le))
... | ↝∘l K' (context-let (promise-↑ _ _ _))
  with _ , refl ← sn↑-k-↑-suc (K-rename _ K) (sn h le) =
  sn'→sn (sn-↑ K (sn'→sn (sn-promise K (kred-↑ K rK) rM (sn (sn↑-k-↑-e (K-rename _ K) (sn h le)) (subst (_≤ _) (sym (k-#↑-let (K-rename _ K'))) z≤n)))))
... | ↝∘↓ K' (context-↓ (promise-↑ _ _ _))
  with _ , refl ← sn↑-k-↑-suc (K-rename _ K) (sn h le) =
  sn'→sn (sn-↑ K (sn'→sn (sn-promise K (kred-↑ K rK) rM (sn (sn↑-k-↑-e (K-rename _ K) (sn h le)) (subst (_≤ _) (sym (k-#↑-↓ (K-rename _ K'))) z≤n)))))
... | ↝∘l _ (context-let (context-promise r)) =
  sn'→sn (sn-promise K (kred-↝ K r rK) rM (h (context-K (K-rename wk₁ K) r)))
... | ↝∘↓ _ (context-↓ (context-promise r)) =
  sn'→sn (sn-promise K (kred-↝ K r rK) rM (h (context-K (K-rename wk₁ K) r)))

cred-promise : CRedSub' M → CRedSub' N → CRed (promise op ↦ M `in N)
cred-promise rM rN K rK =
  sn-promise K (kred-let K rK (credsub'-r rN)) (credsub'-r rM)
    (sn→sn↑ (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (credsub'→cred rN))))

cred→sn : CRed M → SN' M
cred→sn rM = subst SN' ren-id-m (rM id (λ _ ()))

cred-return : VRed V → CRed (return V)
cred-return rV K rK = subst (λ z → SN' (z aₖ return _)) (ren-id-k K) (rK (vred-r rV))

sn-await : (K : Γ ⊢K⦂ Y ⊸ Z) → SN (K aₖ N [ ids [ V ]s ]m) → SN' (K aₖ await ⟨ V ⟩ until N)
sn-await K s r with aₖ→`aₖ K r
... | ↝id (await-promise _ _) = s
... | ↝∘l K (let-await _ _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aₖ let= _ `in z)) (wk₂wk₁M[liftids[W]] _ _) s))
... | ↝∘↓ K (↓-await _ _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aₖ ↓ _ z _)) (wk₁V[ids[W]] _ _) s))
... | ↝∘l _ (context-let (await-promise _ _)) = s
... | ↝∘↓ _ (context-↓ (await-promise _ _)) = s

ared-await : (K : Γ ⊢K⦂ X ⊸ Y) → KRed K → CRedSub' N → ARed K N
ared-await K rK rN rV = sn-await (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rN rV)))

cred-await : VRed V → CRedSub' N → CRed (await V until N)
cred-await rV rN K rK = rV K _ (ared-await K rK (credsub'-r rN))

vred-⟨⟩ : VRed V → VRed ⟨ V ⟩
vred-⟨⟩ rV K N rK = subst₂ (λ z w → SN' (z aₖ await ⟨ V-rename _ _ ⟩ until w)) (ren-id-k K) ren-id-l (rK (vred-r rV))

SubRed : (s : Sub Γ Γ') → Set
SubRed {Γ} s = {X : Type} (x : X ∈ Γ) → VRed (s x)

VRedSub : Γ ⊢V⦂ X → Set
VRedSub {Γ} V = {Γ' : Ctx} {s : Sub Γ Γ'} → SubRed s → VRed (V [ s ]v)

CRedSub : Γ ⊢M⦂ X → Set
CRedSub {Γ} M = {Γ' : Ctx} {s : Sub Γ Γ'} → SubRed s → CRed (M [ s ]m)

subred-⨟ : SubRed s → SubRed (s ⨟ ren r)
subred-⨟ {r = r} rs x = subst VRed (sym ren-rename-v) (vred-r (rs x))

subred-[]s : SubRed s → VRed V → SubRed (s [ V ]s)
subred-[]s rs rV Hd = rV
subred-[]s rs rV (Tl x) = rs x

cred-⨟ : SubRed s → CRedSub M → CRedSub' (M [ lift s ]m)
cred-⨟ rs rM rV K rK = subst (λ z → SN' (K aₖ M-rename _ z)) eq (rM (subred-[]s (subred-⨟ rs) rV) K rK)
  where
  eq : M [ (s ⨟ ren r) [ V ]s ]m
       ≡
       M-rename (wk₂ r) (M [ lift s ]m) [ ids [ V ]s ]m
  eq {M = M} {s = s} {r = r} {V = V} =
    begin
      M [ (s ⨟ ren r) [ V ]s ]m
    ≡⟨ M[lifts][ids[V]] _ _ ⟩
      M [ lift (s ⨟ ren r) ]m [ ids [ V ]s ]m
    ≡⟨ cong (_[ ids [ V ]s ]m) (cong-sub-m (λ x → trans (sym (lift-⨟ x)) (cong-sub-v {V = lift s x} (λ {Hd → refl; (Tl x) → refl})))) ⟩
      M [ lift s ⨟ ren (wk₂ r) ]m [ ids [ V ]s ]m
    ≡⟨ cong (_[ ids [ V ]s ]m) (sym sub-sub-m) ⟩
      M [ lift s ]m [ ren (wk₂ r) ]m [ ids [ V ]s ]m
    ≡⟨ cong (_[ ids [ V ]s ]m) ren-rename-m ⟩
      M-rename (wk₂ r) (M [ lift s ]m) [ ids [ V ]s ]m
    ∎

fund-v : (V : Γ ⊢V⦂ X) → VRedSub V

fund-m : (M : Γ ⊢M⦂ X) → CRedSub M

fund-v (` x) rs = rs x
fund-v (`` c) rs = tt
fund-v (ƛ M) rs = vred-ƛ (cred-⨟ rs (fund-m M))
fund-v ⟨ V ⟩ rs = vred-⟨⟩ (fund-v V rs)

fund-m (return V) rs = cred-return (fund-v V rs)
fund-m (V · W) rs = subst (λ z → CRed (z · _)) ren-id-v (fund-v V rs (fund-v W rs))
fund-m (↑ op V M) rs = cred-↑ (fund-m M rs)
fund-m (promise op ↦ M `in N) rs = cred-promise (cred-⨟ rs (fund-m M)) (cred-⨟ rs (fund-m N))
fund-m (await V until M) rs = cred-await (fund-v V rs) (cred-⨟ rs (fund-m M))
fund-m (let= M `in N) rs = cred-let (fund-m M rs) (cred-⨟ rs (fund-m N))
fund-m (↓ op V M) rs = cred-↓ (fund-m M rs)

all-terms-red : (M : Γ ⊢M⦂ X) → CRed M
all-terms-red M rewrite sym (sub-id-m {M = M}) = fund-m M vred-var

strong-norm : (M : Γ ⊢M⦂ X) → SN M
strong-norm M = sn'→sn (cred→sn (all-terms-red M))