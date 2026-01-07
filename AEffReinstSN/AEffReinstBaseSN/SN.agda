{-# OPTIONS --guardedness #-}

open import AEffReinstSN.AEffReinstBaseSN.AEff
open import AEffReinstSN.AEffReinstBaseSN.Continuations
open import AEffReinstSN.AEffReinstBaseSN.SubstitutionProperties

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)

module AEffReinstSN.AEffReinstBaseSN.SN where

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

KRed : Γ ⊢K⦂ X ⊸ Y [ n ] → Set

ARed : Γ ⊢K⦂ Y ⊸ Z [ n ] → Γ ∷ X ⊢M⦂ Y → Set

SRed : Γ ⊢K⦂ Z ⊸ U [ n ] → Γ ∷ X ⊢M⦂ Z → Γ ∷ Y ⊢M⦂ Z → Set

VRed {Γ} {``` _} V =
  ⊤
VRed {Γ} {𝟙} V =
  ⊤
VRed {Γ} {X ⇒ Y} V =
  {W : Γ ⊢V⦂ X} → VRed W → CRed (V · W)
VRed {Γ} {⟨ X ⟩} V =
  {Y Z : Type} {n : ℕ} (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) (N : Γ ∷ X ⊢M⦂ Y) → ARed K N → SN' (K aK (await V until N))
VRed {Γ} {X + Y} V =
  {Z U : Type} {n : ℕ} (K : Γ ⊢K⦂ Z ⊸ U [ n ]) (M : Γ ∷ X ⊢M⦂ Z) (N : Γ ∷ Y ⊢M⦂ Z) →
    SRed K M N → SN' (K aK (match+ V M N))

CRed {Γ} {X} M =
  {Y : Type} {n : ℕ} (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → SN' (K aK M)

KRed {Γ} {X} id =
  ⊤
KRed {Γ} {X} (K ∘l N) =
  {V : Γ ⊢V⦂ X} → VRed V → SN' (K aK N [ ids [ V ]s ]m)
KRed (K ∘↓ op , V) =
  KRed K
KRed (K ∘c) =
  KRed K

ARed {Γ} {X = X} K N =
  {V : Γ ⊢V⦂ X} → VRed V → SN' (K aK (await ⟨ V ⟩ until N))

SRed {Γ} {X = X} {Y = Y} K M N =
  ({V : Γ ⊢V⦂ X} → VRed V → SN' (K aK (match+ (inl V) M N)))
  ×
  ({V : Γ ⊢V⦂ Y} → VRed V → SN' (K aK (match+ (inr V) M N)))

CRedSub : Γ ∷ X ⊢M⦂ Y → Set
CRedSub {Γ} {X} M = {V : Γ ⊢V⦂ X} → VRed V → CRed (M [ ids [ V ]s ]m)

vred-ƛ  : CRedSub M → VRed (ƛ M)
vred-ƛ f rV K rK r with aK→`aK K r
... | `id (apply _ _) = sn'→sn (f rV K rK)
... | `aKl _ (context-T _ (apply _ _)) = sn'→sn (f rV K rK)
... | `aK↓ _ (context-T _ (apply _ _)) = sn'→sn (f rV K rK)
... | `aKc _ (context-T _ (apply _ _)) = sn'→sn (f rV K rK)

cred→sn' : CRed M → SN' M
cred→sn' rM = rM id tt

sn-★-await : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
             ----------------
             SN' (K aK (await ★ until N))
sn-★-await K r with aK→`aK K r
... | `aKl K (T-await _ _ _) = sn'→sn (sn-★-await K)
... | `aK↓ K (T-await _ _ _) = sn'→sn (sn-★-await K)
... | `aKc K (T-await _ _ _) = sn'→sn (sn-★-await K)

vred-★ : VRed {Γ} {⟨ X ⟩} ★
vred-★ K _ _ = sn-★-await K

kred-let : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
           KRed K →
           CRedSub N →
           ---------------
           KRed (K ∘l N)
kred-let K rK rN rV = rN rV K rK

cred-let : CRed M → CRedSub N → CRed (let= M `in N)
cred-let rM rN K rK = rM (K ∘l _) (kred-let K rK rN)

cred-↓ : CRed M → CRed (↓ op V M)
cred-↓ rM K = rM (K ∘↓ _ , _)

cred-coerce : CRed M → CRed (coerce M)
cred-coerce rM K = rM (K ∘c)

sn-return : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
            SN (K aK N [ ids [ V ]s ]m) →
            --------------------------
            SN' (K aK (let= return V `in N))
sn-return K s r with aK→`aK K r
... | `id (let-return _ _) = s
... | `aKl _ (context-T _ (let-return _ _)) = s
... | `aK↓ _ (context-T _ (let-return _ _)) = s
... | `aKc _ (context-T _ (let-return _ _)) = s

sn-coerce : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
            SN (K aK (return V)) →
            --------------------------
            SN' (K aK (coerce (return V)))
sn-coerce K s r with aK→`aK K r
... | `id (coerce-return _) = s
... | `aKl _ (context-T _ (coerce-return _)) = s
... | `aK↓ _ (context-T _ (coerce-return _)) = s
... | `aKc _ (context-T _ (coerce-return _)) = s

cred-return : VRed V → CRed (return V)
cred-return rV K rK r with aK→`aK K r
... | `aKl _ (let-return _ _) = sn'→sn (rK rV)
... | `aK↓ K (↓-return _ _) = sn'→sn (cred-return rV K rK)
... | `aKc K (coerce-return _) = sn'→sn (cred-return rV K rK)

sn-↑ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) →
       SN (K aK M) →
       --------------
       SN' (K aK (↑ op V M))
sn-↑ K (sn f) r with aK→`aK K r
... | `id (↑-discard _) = sn f
... | `id (context-↑ r) = sn'→sn (sn-↑ id (f r))
... | `aKl K (T-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | `aK↓ K (T-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | `aKc K (T-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | `aKl _ (context-T _ (↑-discard _)) = sn f
... | `aK↓ _ (context-T _ (↑-discard _)) = sn f
... | `aKc _ (context-T _ (↑-discard _)) = sn f
... | `aKl _ (context-T _ (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))
... | `aK↓ _ (context-T _ (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))
... | `aKc _ (context-T _ (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))

sn-match+-inl : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
                SN (K aK M [ ids [ V ]s ]m) →
                ----------------------------
                SN' (K aK (match+ (inl V) M N))
sn-match+-inl K s r with aK→`aK K r
... | `id (match+-inl _ _ _) = s
... | `aKl _ (context-T _ (match+-inl _ _ _)) = s
... | `aK↓ _ (context-T _ (match+-inl _ _ _)) = s
... | `aKc _ (context-T _ (match+-inl _ _ _)) = s

sn-match+-inr : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
                SN (K aK N [ ids [ V ]s ]m) →
                ----------------------------
                SN' (K aK (match+ (inr V) M N))
sn-match+-inr K s r with aK→`aK K r
... | `id (match+-inr _ _ _) = s
... | `aKl _ (context-T _ (match+-inr _ _ _)) = s
... | `aK↓ _ (context-T _ (match+-inr _ _ _)) = s
... | `aKc _ (context-T _ (match+-inr _ _ _)) = s

sred-match+ : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
              KRed (K ∘l M) →
              KRed (K ∘l N) →
              ---------------
              SRed K M N
sred-match+ K rKM rKN = (λ rV → sn-match+-inl K (sn'→sn (rKM rV))) , (λ rV → sn-match+-inr K (sn'→sn (rKN rV)))

cred-match+ : VRed V →
              CRedSub M →
              CRedSub N →
              ------------------
              CRed (match+ V M N)
cred-match+ rV rM rN K rK = rV K _ _ (sred-match+ K (kred-let K rK rM) (kred-let K rK rN))

kred-comm-l : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
              KRed (K ∘l M ∘l N) →
              -------------------
              KRed (K ∘l (let= N `in (M-rename (wk₂ wk₁) M)))
kred-comm-l {M = M} K rK {V} rewrite ⌊ eq₇ (⊢M M) V ⌋m = rK

kred-comm-↓ : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
              KRed (K ∘↓ op , V ∘l N) →
              -------------------
              KRed (K ∘l (↓ op (V-rename wk₁ V) N))
kred-comm-↓ {V = V} K rK {W} rewrite ⌊ eq₁ (⊢V V) W ⌋v = rK

kred-comm-c : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
              KRed (K ∘c ∘l N) →
              -------------------
              KRed (K ∘l (coerce N))
kred-comm-c K rK = rK

kred-↝ : M ↝ N →
         (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
         KRed (K ∘l M) →
         ---------------
         KRed (K ∘l N)
kred-↝ r K rK rV = sn→sn' (rK rV (context-K K (sub-↝ _ r)))

eq : M-rename wk₁ (M-rename wk₁ M) [ lift (ids [ V' ]s) ]m [ ids [ W ]s ]m ≡ M
eq {M = M} {V' = V'} {W = W} = trans (cong (_[ _ ]m) (⌊ eq₄ _ _ _ ⌋m)) (trans ⌊ eq₁ _ _ ⌋m ⌊ eq₁ _ _ ⌋m)

sn-promise : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
             KRed (K ∘l N) →
             CRedSub M →
             SN (K aK N [ ids [ ★ ]s ]m) →
             ---------------------------
             SN' (K aK (promise op ↦ M `in N))
sn-promise {N = N} {op = op} {M = M} K rK rM (sn h) r with aK→`aK K r
... | `id (promise-↑ V _ _) =
  sn'→sn (sn-↑ id (sn'→sn (sn-promise id (kred-↝ (↑-discard V) id rK) rM (h (↑-discard _)))))
... | `id (context-promise r) =
  sn'→sn (sn-promise id (kred-↝ r id rK) rM (h (sub-↝ _ r)))
... | `aKl K (T-promise _ _ _) =
  sn'→sn (sn-promise K (kred-comm-l K rK) rM (sn'→sn (kred-comm-l K rK vred-★)))
... | `aKl _ (context-T _ (promise-↑ V _ _)) =
  sn'→sn (sn-↑ K (sn'→sn (sn-promise K (kred-↝ (↑-discard V) K rK) rM (h (context-K K (↑-discard _))))))
... | `aKl _ (context-T _ (context-promise r)) =
  sn'→sn (sn-promise K (kred-↝ r K rK) rM (h (context-K K (sub-↝ _ r))))
... | `aK↓ K (T-promise _ _ _) =
  sn'→sn (sn-promise K (kred-comm-↓ K rK) rM (sn'→sn (kred-comm-↓ K rK vred-★)))
... | `aK↓ K (↓-promise-op Vop _ _) =
  sn'→sn (rM tt (K ∘l _ ∘l _ ∘c)
    (λ rV → rV (K ∘l _) _ _ (sred-match+ (K ∘l _)
      (λ rV → cred-return rV (K ∘l _) (kred-comm-↓ K rK))
      (λ _ → subst (λ z → SN' (K aK (let= coerce z `in (T↓ _ (V-rename Tl Vop) aT N))))
        (sym (eq {M = promise _ ↦ _ `in return (` Hd)}))
        (sn-promise (K ∘l _ ∘c)
          (λ {V} rV → cred-coerce (cred-return {V = V} rV) (K ∘l _) (kred-comm-↓ K rK)) rM
          (sn'→sn (sn-coerce (K ∘l _) (sn'→sn
            (sn-return K (subst (λ z → SN (K aK ↓ op z _)) (sym ⌊ eq₁ _ _ ⌋v) (sn h)))))))))))
... | `aK↓ _ (context-T _ (promise-↑ V _ _)) =
  sn'→sn (sn-↑ K (sn'→sn (sn-promise K (kred-↝ (↑-discard V) K rK) rM (h (context-K K (↑-discard _))))))
... | `aK↓ _ (context-T _ (context-promise r)) =
  sn'→sn (sn-promise K (kred-↝ r K rK) rM (h (context-K K (sub-↝ _ r))))
... | `aKc K (T-promise _ _ _) =
  sn'→sn (sn-promise K (kred-comm-c K rK) rM (sn'→sn (kred-comm-c K rK vred-★)))
... | `aKc _ (context-T _ (promise-↑ V _ _)) =
  sn'→sn (sn-↑ K (sn'→sn (sn-promise K (kred-↝ (↑-discard V) K rK) rM (h (context-K K (↑-discard _))))))
... | `aKc _ (context-T _ (context-promise r)) =
  sn'→sn (sn-promise K (kred-↝ r K rK) rM (h (context-K K (sub-↝ _ r))))

sn-await : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
           SN (K aK N [ ids [ V ]s ]m) →
           -----------------------
           SN' (K aK (await ⟨ V ⟩ until N))
sn-await K s r with aK→`aK K r
... | `id (await-promise _ _) = s
... | `aKl K (T-await _ _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aK (let= _ `in z))) (sym ⌊ eq₇ _ _ ⌋m) s))
... | `aK↓ K (T-await _ _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aK (↓ _ z _))) (sym ⌊ eq₁ _ _ ⌋v) s))
... | `aKc K (T-await _ _ _) = sn'→sn (sn-await K s)
... | `aKl _ (context-T _ (await-promise _ _)) = s
... | `aK↓ _ (context-T _ (await-promise _ _)) = s
... | `aKc _ (context-T _ (await-promise _ _)) = s

cred-↑ : CRed M → CRed (↑ op V M)
cred-↑ rM K rK = sn-↑ K (sn'→sn (rM K rK))

cred-promise : CRedSub M →
               CRedSub N →
               ---------
               CRed (promise op ↦ M `in N)
cred-promise rM rN K rK = sn-promise K (λ rV → rN rV K rK) rM (sn'→sn (rN vred-★ K rK))

cred-await : VRed V →
             CRedSub N →
             ---------
             CRed (await V until N)
cred-await rV rN K rK = rV K _ (λ rW → sn-await K (sn'→sn (rN rW K rK)))

sn-var-await : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
               ----------------
               SN' (K aK (await ` x until N))
sn-var-await K r with aK→`aK K r
... | `aKl K (T-await _ _ _) = sn'→sn (sn-var-await K)
... | `aK↓ K (T-await _ _ _) = sn'→sn (sn-var-await K)
... | `aKc K (T-await _ _ _) = sn'→sn (sn-var-await K)

vred-var : (x : X ∈ Γ) → VRed (` x)
vred-var {X = ``` c} x = tt
vred-var {X = 𝟙} x = tt
vred-var {X = X ⇒ Y} x rV K rK r with aK→`aK K r
... | `aKl _ (context-T _ ())
... | `aK↓ _ (context-T _ ())
... | `aKc _ (context-T _ ())
vred-var {X = ⟨ X ⟩} x K _ rA = sn-var-await K
vred-var {X = X + Y} x K M N rS r with aK→`aK K r
... | `aKl _ (context-T T ())
... | `aK↓ _ (context-T T ())
... | `aKc _ (context-T T ())

SubRed : (s : Sub Γ Γ') → Set
SubRed {Γ} s = {X : Type} (x : X ∈ Γ) → VRed (s x)

cred-⨟ : SubRed s →
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
fund-v ⟨ V ⟩ rs _ _ rA =
  rA (fund-v V rs)
fund-v (inl V) rs _ _ _ (rS1 , _) =
  rS1 (fund-v V rs)
fund-v (inr V) rs _ _ _ (_ , rS2) =
  rS2 (fund-v V rs)
fund-v ★ rs =
  vred-★
fund-v u rs =
  tt

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
  cred-promise (cred-⨟ rs (fund-m M)) (cred-⨟ rs (fund-m N)) 
fund-m (await V until M) rs =
  cred-await (fund-v V rs) (cred-⨟ rs (fund-m M))
fund-m (match+ V M N) rs =
  cred-match+ (fund-v V rs) (cred-⨟ rs (fund-m M)) (cred-⨟ rs (fund-m N))
fund-m (coerce M) rs =
  cred-coerce (fund-m M rs)

all-terms-red : (M : Γ ⊢M⦂ X) → CRed M
all-terms-red M rewrite sym ⌊ sub-id {TT = ⊢M M} ⌋m = fund-m M vred-var

strong-norm : (M : Γ ⊢M⦂ X) → SN M
strong-norm M = sn'→sn (cred→sn' (all-terms-red M))
