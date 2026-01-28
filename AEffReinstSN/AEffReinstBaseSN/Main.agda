{-# OPTIONS --guardedness #-}

open import AEffReinstSN.AEffReinstBaseSN.AEff
open import AEffReinstSN.AEffReinstBaseSN.StronglyNormalising
open import AEffReinstSN.AEffReinstBaseSN.SubstitutionProperties
open import AEffReinstSN.AEffReinstBaseSN.Continuations

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (_×_; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂) renaming (module ≡-Reasoning to Eq)
open Eq using (begin_; step-≡-⟩; _∎)

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

open import Function using (_∘_)

module AEffReinstSN.AEffReinstBaseSN.Main where

subst₃ : ∀ {A B C : Set} (D : A → B → C → Set) {x y z w u v} → x ≡ y → z ≡ w → u ≡ v → D x z u → D y w v
subst₃ _ refl refl refl z = z

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
  {Γ' : Ctx} {r : Ren Γ Γ'} {W : Γ' ⊢V⦂ X} → VRed W → CRed (V-rename r V · W)
VRed {Γ} {⟨ X ⟩} V =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Y Z : Type} {n : ℕ} (K : Γ' ⊢K⦂ Y ⊸ Z [ n ]) (N : Γ' ∷ X ⊢M⦂ Y) → ARed K N → SN' (K aₖ await V-rename r V until N)
VRed {Γ} {X + Y} V =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Z U : Type} {n : ℕ} (K : Γ' ⊢K⦂ Z ⊸ U [ n ]) (M : Γ' ∷ X ⊢M⦂ Z) (N : Γ' ∷ Y ⊢M⦂ Z) → SRed K M N → SN' (K aₖ match+ (V-rename r V) M N)

CRed {Γ} {X} M =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Y : Type} {n : ℕ} (K : Γ' ⊢K⦂ X ⊸ Y [ n ]) → KRed K → SN' (K aₖ M-rename r M)

KRed {Γ} {X} K =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → SN' (K-rename r K aₖ return V)

ARed {Γ} {Y} {Z} {n} {X} K N =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → SN' (K-rename r K aₖ await ⟨ V ⟩ until M-rename (wk₂ r) N)

SRed {Γ} {X = X} {Y = Y} K M N =
  ({Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → SN' (K-rename r K aₖ match+ (inl V) (M-rename (wk₂ r) M) (M-rename (wk₂ r) N)))
  ×
  ({Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ Y} → VRed V → SN' (K-rename r K aₖ match+ (inr V) (M-rename (wk₂ r) M) (M-rename (wk₂ r) N)))

CRedSub' : Γ ∷ X ⊢M⦂ Y → Set
CRedSub' {Γ} {X} M =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → CRed (M-rename (wk₂ r) M [ id-subst [ V ]s ]m)

vred-r : VRed V → VRed (V-rename r V)
vred-r {_} {``` x} rV = tt
vred-r {_} {𝟙} rV = tt
vred-r {_} {X ⇒ Y} rV rW K rK = subst SN' (cong (λ z → K aₖ V-rename _ z · _) (sym ren-ren-v)) (rV rW K rK)
vred-r {_} {⟨ X ⟩} rV K N rA = subst SN' (cong (λ z → K aₖ await z until _) (sym ren-ren-v)) (rV K N rA)
vred-r {_} {X + Y} rV K M N rS = subst SN' (cong (λ z → K aₖ match+ z _ _) (sym ren-ren-v)) (rV K M N rS)

kred-r : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → KRed (K-rename r K)
kred-r K rK rV = subst SN' (cong (_aₖ _) (sym (ren-ren-k K))) (rK rV)

credsub'-r : CRedSub' M → CRedSub' (M-rename (wk₂ r) M)
credsub'-r rM rV K rK = subst (λ z → SN' (K aₖ M-rename _ (z [ id-subst [ _ ]s ]m))) (sym ren-ren-l) (rM rV K rK)

sn-var-await : {x : ⟨ X ⟩ ∈ Γ} (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) → SN' (K aₖ await ` x until N)
sn-var-await K r with aₖ→`aₖ K r
... | ↝∘l K (let-await _ _ _) = sn'→sn (sn-var-await K)
... | ↝∘↓ K (↓-await _ _ _) = sn'→sn (sn-var-await K)

vred-var : (x : X ∈ Γ) → VRed (` x)
vred-var {``` _} _ = tt
vred-var {𝟙} _ = tt
vred-var {_ ⇒ _} _ _ K _ r with aₖ→`aₖ K r
... | ↝∘l _ (context-let ())
... | ↝∘↓ _ (context-↓ ())
vred-var {⟨ _ ⟩} _ K _ _ = sn-var-await K
vred-var {_ + _} _ K _ _ _ r with aₖ→`aₖ K r
... | ↝∘l _ (context-let ())
... | ↝∘↓ _ (context-↓ ())

cred-kred : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → CRed M → SN' (K aₖ M)
cred-kred K rK rM = subst (λ z → SN' (K aₖ z)) ren-id-m (rM K rK)

credsub'→cred : CRedSub' M → CRed (M-rename (wk₂ r) M)
credsub'→cred rM =
  subst CRed
    (trans (sub-ren-m (λ {Hd → refl; (Tl x) → refl})) (cong (M-rename _) sub-id-m))
    (rM (vred-var Hd))

sn-ƛ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → SN (K aₖ M [ id-subst [ W ]s ]m) → SN' (K aₖ ƛ M · W)
sn-ƛ K s r with aₖ→`aₖ K r
... | ↝id (apply _ _) = s
... | ↝∘l _ (context-let (apply _ _)) = s
... | ↝∘↓ _ (context-↓ (apply _ _)) = s

vred-ƛ : CRedSub' M → VRed (ƛ M)
vred-ƛ rM rW K rK = sn-ƛ K (subst (λ z → SN (K aₖ z [ id-subst [ _ ]s ]m)) (sym ren-ren-l) (sn'→sn (cred-kred K rK (rM (vred-r rW)))))

sn-let-return : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → SN (K aₖ N [ id-subst [ V ]s ]m) → SN' (K aₖ let= return V `in N)
sn-let-return K s r with aₖ→`aₖ K r
... | ↝id (let-return _ _) = s
... | ↝∘l _ (context-let (let-return _ _)) = s
... | ↝∘↓ _ (context-↓ (let-return _ _)) = s

kred-let : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → CRedSub' N → KRed (K ∘l N)
kred-let K rK rN rV = sn-let-return (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rN rV)))

cred-let : CRed M → CRedSub' N → CRed (let= M `in N)
cred-let rM rN K rK = rM (K ∘l _) (kred-let K rK (credsub'-r rN))

sn-↓ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → SN (K aₖ return V) → SN' (K aₖ ↓ op W (return V))
sn-↓ K s r with aₖ→`aₖ K r
... | ↝id (↓-return _ _) = s
... | ↝∘l _ (context-let (↓-return _ _)) = s
... | ↝∘↓ _ (context-↓ (↓-return _ _)) = s

kred-↓ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → KRed (K ∘↓ op [ V ])
kred-↓ K rK rV = sn-↓ (K-rename _ K) (sn'→sn (rK rV))

cred-↓ : CRed M → CRed (↓ op V M)
cred-↓ rM K rK = rM (K ∘↓ _ [ _ ]) (kred-↓ K rK)

cred-return : VRed V → CRed (return V)
cred-return rV K rK = subst (λ z → SN' (z aₖ return _)) (ren-id-k K) (rK (vred-r rV))

sn-↑ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → SN (K aₖ M) → SN' (K aₖ ↑ op V M)
sn-↑ K (sn f) r with aₖ→`aₖ K r
... | ↝id (context-↑ r) = sn'→sn (sn-↑ {n = 0} id (f r))
... | ↝∘l K (let-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | ↝∘l _ (context-let (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))
... | ↝∘↓ K (↓-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | ↝∘↓ _ (context-↓ (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))

cred-↑ : CRed M → CRed (↑ op V M)
cred-↑ rM K rK = sn-↑ K (sn'→sn (rM K rK))

sn-match+-inl : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
                SN (K aₖ M [ id-subst [ V ]s ]m) →
                ----------------------------
                SN' (K aₖ match+ (inl V) M N)

sn-match+-inl K s r with aₖ→`aₖ K r
... | ↝id (match+-inl _ _ _) = s
... | ↝∘l _ (context-let (match+-inl _ _ _)) = s
... | ↝∘↓ _ (context-↓ (match+-inl _ _ _)) = s

sn-match+-inr : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
                SN (K aₖ N [ id-subst [ V ]s ]m) →
                ----------------------------
                SN' (K aₖ match+ (inr V) M N)

sn-match+-inr K s r with aₖ→`aₖ K r
... | ↝id (match+-inr _ _ _) = s
... | ↝∘l _ (context-let (match+-inr _ _ _)) = s
... | ↝∘↓ _ (context-↓ (match+-inr _ _ _)) = s

sred-match+ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → CRedSub' M → CRedSub' N → SRed K M N
sred-match+ K rK rM rN =
  (λ rV → sn-match+-inl (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rM rV)))) ,
  (λ rV → sn-match+-inr (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rN rV))))

cred-match+ : VRed V → CRedSub' M → CRedSub' N → CRed (match+ V M N)
cred-match+ rV rM rN K rK = rV K _ _ (sred-match+ K rK (credsub'-r rM) (credsub'-r rN))

vred-inl : VRed V → VRed (inl {Y = Y} V)
vred-inl rV K M N (sK , _) = subst₃ (λ z w u → SN' (z aₖ match+ _ w u)) (ren-id-k K) ren-id-l ren-id-l (sK (vred-r rV))

vred-inr : VRed V → VRed (inr {X = X} V)
vred-inr rV K M N (_ , sK) = subst₃ (λ z w u → SN' (z aₖ match+ _ w u)) (ren-id-k K) ren-id-l ren-id-l (sK (vred-r rV))

sn-await : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) → SN (K aₖ N [ id-subst [ V ]s ]m) → SN' (K aₖ await ⟨ V ⟩ until N)
sn-await K s r with aₖ→`aₖ K r
... | ↝id (await-promise _ _) = s
... | ↝∘l K (let-await _ _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aₖ let= _ `in z)) (wk₂wk₁M[liftid-subst[W]] _ _) s))
... | ↝∘↓ K (↓-await _ _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aₖ ↓ _ z _)) (wk₁V[id-subst[W]] _ _) s))
... | ↝∘l _ (context-let (await-promise _ _)) = s
... | ↝∘↓ _ (context-↓ (await-promise _ _)) = s

ared-await : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → CRedSub' N → ARed K N
ared-await K rK rN rV = sn-await (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rN rV)))

cred-await : VRed V → CRedSub' N → CRed (await V until N)
cred-await rV rN K rK = rV K _ (ared-await K rK (credsub'-r rN))

vred-⟨⟩ : VRed V → VRed ⟨ V ⟩
vred-⟨⟩ rV K N rK = subst₂ (λ z w → SN' (z aₖ await ⟨ V-rename _ _ ⟩ until w)) (ren-id-k K) ren-id-l (rK (vred-r rV))

kred-comm-let : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
                KRed (K ∘l L ∘l N) →
                ---------------------------------------------
                KRed (K ∘l (let= N `in M-rename (wk₂ wk₁) L))

kred-comm-let K rK rV =
  sn-let-return (K-rename _ K)
    (subst (λ z → SN (K-rename _ K aₖ let= _ `in z))
      eq (rK rV (context-K (K-rename _ K ∘l _) (let-return _ _))))
  where
  eq : M-rename (wk₂ r) L
       ≡
       M-rename (wk₂ (wk₂ r)) (M-rename (wk₂ wk₁) L) [ lift (id-subst [ V ]s) ]m

  eq {r = r} {L = L} {V = V} = 
    begin
      M-rename (wk₂ r) L
    ≡⟨ wk₂wk₁M[liftid-subst[W]] _ _ ⟩
      M-rename (wk₂ wk₁) (M-rename (wk₂ r) L) [ lift (id-subst [ V ]s) ]m
    ≡⟨ cong (_[ _ ]m) (trans ren-ren-l (sym ren-ren-l)) ⟩
      M-rename (wk₂ (wk₂ r)) (M-rename (wk₂ wk₁) L) [ lift (id-subst [ V ]s) ]m
    ∎

kred-comm-↓ : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
              KRed (K ∘↓ op [ V ] ∘l N) →
              ----------------------
              KRed (K ∘l ↓ op (V-rename wk₁ V) N)

kred-comm-↓ K rK rV =
  sn-let-return (K-rename _ K)
    (subst (λ z → SN (K-rename _ K aₖ ↓ _ z _))
      eq (rK rV (context-K (K-rename _ K ∘↓ _ [ _ ]) (let-return _ _))))
  where
  eq : V-rename r W
       ≡
       V-rename (wk₂ r) (V-rename wk₁ W) [ id-subst [ V ]s ]v

  eq {r = r} {W = W} {V = V} = 
    begin
      V-rename r W
    ≡⟨ wk₁V[id-subst[W]] _ _ ⟩
      V-rename wk₁ (V-rename r W) [ id-subst [ V ]s ]v
    ≡⟨ cong (_[ id-subst [ V ]s ]v) (trans (ren-ren-v {V = W}) (sym ren-ren-v)) ⟩
      V-rename (wk₂ r) (V-rename wk₁ W) [ id-subst [ V ]s ]v
    ∎

kred-↝ : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
         M ↝↝ N →
         KRed (K ∘l M) →
         --------------
         KRed (K ∘l N)

kred-↝ K r rK rV =
  sn-let-return (K-rename _ K)
    (sn→sn'
      (rK rV (context-K (K-rename _ K) (let-return _ _)))
      (context-K (K-rename _ K) (sub-↝↝ _ (ren-↝↝ _ r))))

sn-k-↑-e : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) → SN (K aₖ ↑ op V M) → SN' (K aₖ M)
sn-k-↑-e K (sn sM) r with aₖ→`aₖ K r
... | ↝id r = sn'→sn (sn-k-↑-e id (sM (context-↑ r)))
... | ↝∘l K r = sn-k-↑-e K (sM (context-K K (let-↑ _ _ _))) (context-K K r)
... | ↝∘↓ K r = sn-k-↑-e K (sM (context-K K (↓-↑ _ _ _))) (context-K K r)

sni-k-↑-e' : (K : Γ ⊢K⦂ Y ⊸ Z [ k ]) → SNi (K aₖ ↑ op V M) (suc n) → {L : Γ ⊢M⦂ Z} → K aₖ M ↝↝ L → SNi L n

sni-k-↑-e : (K : Γ ⊢K⦂ Y ⊸ Z [ k ]) → SNi (K aₖ ↑ op V M) n → SNi (K aₖ M) n

sni-k-↑-e' K (sn sM) r with aₖ→`aₖ K r
... | ↝id r = sni-k-↑-e id (sM (context-↑ r))
... | ↝∘l K r with sn sM ← sni-k-↑-e K (sM (context-K K (let-↑ _ _ _))) = sni-≤ (n≤1+n _) (sM (context-K K r))
... | ↝∘↓ K r with sn sM ← sni-k-↑-e K (sM (context-K K (↓-↑ _ _ _))) = sni-≤ (n≤1+n _) (sM (context-K K r))

sni-k-↑-e {n = suc n} K sM = sn (sni-k-↑-e' K sM)

kred-↑ : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) → KRed (K ∘l ↑ op V M) → KRed (K ∘l M)
kred-↑ K rK rV =
  sn-let-return (K-rename _ K)
    (sn'→sn (sn-k-↑-e (K-rename _ K) (rK rV (context-K (K-rename _ K) (let-return _ _)))))

v-ren-lemma : V-rename (wk₂ wk₁) V [ id-subst [ ` Hd ]s ]v ≡ V
v-ren-lemma {V = V} = trans (sub-ren-v {V = V} (λ {Hd → refl; (Tl x) → refl})) (trans ren-id-v sub-id-v)

m-ren-lemma : M-rename (wk₂ wk₁) M [ id-subst [ ` Hd ]s ]m ≡ M
m-ren-lemma {M = M} = trans (sub-ren-m {M = M} (λ {Hd → refl; (Tl x) → refl})) (trans ren-id-m sub-id-m)

m-ren-lemma' :
  M-rename (wk₂ (wk₂ r))
    (M-rename (wk₂ (wk₂ (wk₂ r')))
      (M-rename (wk₂ wk₁) (M-rename (wk₂ wk₁) M))
    [ lift (lift (id-subst [ V ]s)) ]m)
  [ lift (id-subst [ V' ]s) ]m
  ≡
  M-rename (wk₂ r) (M-rename (wk₂ r') M)

m-ren-lemma' =
  trans (cong (λ z → M-rename _ (z [ _ ]m) [ _ ]m) (trans (trans ren-ren-l ren-ren-l) (sym (trans ren-ren-l ren-ren-l))))
  (trans (cong (λ z → M-rename _ z [ _ ]m) (wk₂wk₁[M[lifts]] _ _ _))
  (trans (cong (λ z → M-rename _ (M-rename (wk₂ wk₁) z) [ _ ]m) (sym (wk₂wk₁M[liftid-subst[W]] _ _)))
  (trans (cong (_[ _ ]m) (trans ren-ren-l (sym ren-ren-l)))
  (sym (wk₂wk₁M[liftid-subst[W]] _ _)))))

k-ren-lemma : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
              -------------------------
              K-rename (wk₁ {X = X}) (K-rename r (K-rename r' K))
              ≡
              K-rename (wk₂ r) (K-rename (wk₂ r') (K-rename wk₁ K))

k-ren-lemma K =
  trans (ren-ren-k (K-rename _ K))
  (trans (ren-ren-k K)
  (trans (cong-ren-k K (λ {Hd → refl; (Tl x) → refl}))
  (trans (sym (ren-ren-k K))
  (sym (ren-ren-k (K-rename _ K))))))

v-ren-lemma' : V-rename (wk₁ {X = X}) (V-rename r (V-rename r' V))
               ≡
               V-rename (wk₂ r) (V-rename (wk₂ r') (V-rename wk₁ V))

v-ren-lemma' =
  trans ren-ren-v
  (trans ren-ren-v
  (trans (cong-ren-v (λ {Hd → refl; (Tl x) → refl}))
  (trans (sym ren-ren-v)
  (sym ren-ren-v))))

ren-lemma'' : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
  K-rename r (K-rename r' K)
  aₖ
  ↓ op
    (V-rename (wk₂ r) (V-rename (wk₂ r') (V-rename wk₁ V)) [ id-subst [ V' ]s ]v)
    (M-rename (wk₂ r) (M-rename (wk₂ r') N) [ id-subst [ V' ]s ]m)
  ≡
  K-rename (r ∘ r') K
  aₖ
  ↓ op
    (V-rename (r ∘ r') V)
    (M-rename (wk₂ (r ∘ r')) N [ id-subst [ V' ]s ]m)

ren-lemma'' {V = V} K =
  trans (cong (_aₖ _) (ren-ren-k K))
  (trans (cong (λ z → K-rename _ K aₖ ↓ _ (z [ id-subst [ _ ]s ]v) _) (sym (v-ren-lemma' {V = V})))
  (trans (cong (λ z → K-rename _ K aₖ ↓ _ z _) (sym (wk₁V[id-subst[W]] _ _)))
  (trans (cong (λ z → K-rename _ K aₖ ↓ _ z _) ren-ren-v)
  (cong (λ z → K-rename _ K aₖ ↓ _ _ (z [ id-subst [ _ ]s ]m)) ren-ren-l))))

aₖ-ren : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
         ------------------------------
         M-rename r (M-rename r' (K aₖ M))
         ≡
         K-rename r (K-rename r' K) aₖ M-rename r (M-rename r' M)

aₖ-ren id = refl
aₖ-ren (K ∘l x) = aₖ-ren K
aₖ-ren (K ∘↓ op [ x ]) = aₖ-ren K

sn-promise : (K : Γ ⊢K⦂ Y ⊸ Z [ k ]) →
             KRed (K ∘l N) →
             CRedSub' M →
             SNi (K-rename wk₁ K aₖ N) n →
             -----------------------------------
             {L : Γ ⊢M⦂ Z} → K `aₖ promise op ↦ M `in N ↝↝ L → SN L

sn-promise K rK rM (sn h) (↝id (promise-↑ _ _ _)) =
  sn'→sn (sn-↑ K (sn'→sn (λ r → sn-promise K (kred-↑ K rK) rM (sni-k-↑-e id (sn h)) (aₖ→`aₖ K r))))
sn-promise K rK rM (sn h) (↝id (context-promise r)) =
  sn'→sn (λ r' → sn-promise K (kred-↝ K r rK) rM (h (context-K (K-rename wk₁ K) r)) (aₖ→`aₖ K r'))
sn-promise _ rK rM (sn h) (↝∘l K (let-promise _ _ _)) =
  sn'→sn (λ r → sn-promise K (kred-comm-let K rK) rM (sn h) (aₖ→`aₖ K r))
sn-promise K rK rM (sn h) (↝∘l K' (context-let (promise-↑ _ _ _))) =
  sn'→sn (sn-↑ K (sn'→sn (λ r → sn-promise K (kred-↑ K rK) rM (sni-k-↑-e (K-rename _ (K' ∘l _)) (sn h)) (aₖ→`aₖ K r))))
sn-promise K rK rM (sn h) (↝∘l _ (context-let (context-promise r))) =
  sn'→sn (λ r' → sn-promise K (kred-↝ K r rK) rM (h (context-K (K-rename wk₁ K) r)) (aₖ→`aₖ K r'))
sn-promise _ rK rM (sn h) (↝∘↓ K (↓-promise-op _ _ _)) =
  sn'→sn (
    subst (λ z → SN' (K aₖ (let= let= z `in _ `in ↓ _ _ _))) (trans ren-id-m (cong (_[ id-subst [ _ ]s ]m) ren-id-l)) (rM tt (K ∘l _ ∘l _)
    (λ {V = V} rV → sn-let-return (K-rename _ K ∘l _) (subst
       (λ z → SN (K-rename _ K aₖ (let= match+ z (return (` Hd)) (promise _ ↦ _ [ lift (lift (id-subst [ V ]s)) ]m `in return (` Hd)) `in _)))
       ren-id-v (sn'→sn (rV {r = id-ren} (K-rename _ K ∘l _) _ _
        ((λ rV' → sn-match+-inl (K-rename _ (K-rename _ K) ∘l _)
          (sn'→sn
            (sn-let-return
              (K-rename _ (K-rename _ K))
              (subst SN (sym (ren-lemma'' K)) (rK rV' (context-K (K-rename _ K ∘↓ _ [ _ ]) (let-return _ _))))))) ,
        (λ _ → sn-match+-inr (K-rename _ (K-rename _ K) ∘l _)
          (sn'→sn
            (λ r → sn-promise
              (K-rename _ (K-rename _ K) ∘l _)
              (kred-let (K-rename _ (K-rename _ K) ∘l _) (kred-r (K-rename _ K ∘l _) (kred-r (K ∘l _) (kred-comm-↓ K rK))) cred-return)
              (subst CRedSub' (sym m-ren-lemma') (credsub'-r (credsub'-r rM)))
              (sn→sni (sn'→sn (sn-let-return (K-rename _ (K-rename _ (K-rename _ K)))
                (subst₃ (λ z w u → SN (z aₖ ↓ _ w u)) (sym (k-ren-lemma K)) (sym v-ren-lemma) (sym m-ren-lemma)
                  (subst SN (aₖ-ren (K-rename _ K)) (ren-sn (ren-sn (sni→sn (sn h))))))))) (aₖ→`aₖ (K-rename _ (K-rename _ K) ∘l _) r)))))))))))
sn-promise _ rK rM (sn h) (↝∘↓ K (↓-promise-op' _ _ _ _)) =
  sn'→sn (λ r → sn-promise K (kred-comm-↓ K rK) rM (sn h) (aₖ→`aₖ K r))
sn-promise K rK rM (sn h) (↝∘↓ K' (context-↓ (promise-↑ _ _ _))) =
  sn'→sn (sn-↑ K (sn'→sn (λ r → sn-promise K (kred-↑ K rK) rM (sni-k-↑-e (K-rename _ (K' ∘↓ _ [ _ ])) (sn h)) (aₖ→`aₖ K r))))
sn-promise K rK rM (sn h) (↝∘↓ _ (context-↓ (context-promise r))) =
  sn'→sn (λ r' → sn-promise K (kred-↝ K r rK) rM (h (context-K (K-rename wk₁ K) r)) (aₖ→`aₖ K r'))

cred-promise : CRedSub' M → CRedSub' N → CRed (promise op ↦ M `in N)
cred-promise rM rN K rK r =
  sn-promise K (kred-let K rK (credsub'-r rN)) (credsub'-r rM)
    (sn→sni (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (credsub'→cred rN)))) (aₖ→`aₖ K r)

cred→sn : CRed M → SN' M
cred→sn rM = subst SN' ren-id-m (rM id (λ _ ()))

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
       M-rename (wk₂ r) (M [ lift s ]m) [ id-subst [ V ]s ]m

  eq {M = M} {s = s} {r = r} {V = V} =
    begin
      M [ (s ⨟ ren r) [ V ]s ]m
    ≡⟨ M[lifts][id-subst[V]] _ _ ⟩
      M [ lift (s ⨟ ren r) ]m [ id-subst [ V ]s ]m
    ≡⟨ cong (_[ id-subst [ V ]s ]m) (cong-sub-m (λ x → trans (sym (lift-⨟ x)) (cong-sub-v {V = lift s x} (λ {Hd → refl; (Tl x) → refl})))) ⟩
      M [ lift s ⨟ ren (wk₂ r) ]m [ id-subst [ V ]s ]m
    ≡⟨ cong (_[ id-subst [ V ]s ]m) (sym sub-sub-m) ⟩
      M [ lift s ]m [ ren (wk₂ r) ]m [ id-subst [ V ]s ]m
    ≡⟨ cong (_[ id-subst [ V ]s ]m) ren-rename-m ⟩
      M-rename (wk₂ r) (M [ lift s ]m) [ id-subst [ V ]s ]m
    ∎

fund-v : (V : Γ ⊢V⦂ X) → VRedSub V

fund-m : (M : Γ ⊢M⦂ X) → CRedSub M

fund-v (` x) rs = rs x
fund-v (`` c) rs = tt
fund-v (ƛ M) rs = vred-ƛ (cred-⨟ rs (fund-m M))
fund-v ⟨ V ⟩ rs = vred-⟨⟩ (fund-v V rs)
fund-v (inl V) rs = vred-inl (fund-v V rs)
fund-v (inr V) rs = vred-inr (fund-v V rs)
fund-v ★ rs = tt

fund-m (return V) rs = cred-return (fund-v V rs)
fund-m (V · W) rs = subst (λ z → CRed (z · _)) ren-id-v (fund-v V rs (fund-v W rs))
fund-m (↑ op V M) rs = cred-↑ (fund-m M rs)
fund-m (promise op ↦ M `in N) rs = cred-promise (cred-⨟ rs (fund-m M)) (cred-⨟ rs (fund-m N))
fund-m (await V until M) rs = cred-await (fund-v V rs) (cred-⨟ rs (fund-m M))
fund-m (let= M `in N) rs = cred-let (fund-m M rs) (cred-⨟ rs (fund-m N))
fund-m (↓ op V M) rs = cred-↓ (fund-m M rs)
fund-m (match+ V M N) rs = cred-match+ (fund-v V rs) (cred-⨟ rs (fund-m M)) (cred-⨟ rs (fund-m N))

all-terms-red : (M : Γ ⊢M⦂ X) → CRed M
all-terms-red M rewrite sym (sub-id-m {M = M}) = fund-m M vred-var

strong-norm : (M : Γ ⊢M⦂ X) → SN M
strong-norm M = sn'→sn (cred→sn (all-terms-red M))