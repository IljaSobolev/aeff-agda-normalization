open import AEff renaming (``_ to ```_)
open import Types
open import Substitutions
open import Renamings
open import Preservation
open import Finality

open import SubstitutionProperties using (commute-subst-rename-v; commute-subst-rename-m; ren-id-v; ren-id-m; sub-id-v; sub-id-m; sub-↝↝)
open import StrongNormalisation
open import Continuations

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; subst; sym; trans)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)

VRed : {Γ : Ctx}
       (X : Type) →
       Γ ⊢V⦂ X →
       --------------
       Set
CRed : {Γ : Ctx}
       (X : Type) →
       Γ ⊢M⦂ X →
       --------------
       Set
KRed : {Γ : Ctx}
       (X : Type)
       {Y : Type} →
       Γ ⊢K⦂ X ⊸ Y →
       --------------
       Set
ARed : {Γ : Ctx}
       (X : Type)
       {Y Z : Type} →
       Γ ⊢K⦂ X ⊸ Y →
       Γ ∷ Z ⊢M⦂ X →
       --------------
       Set
VRed (`` _) V = ⊤
VRed {Γ} (X ⇒ Y) V = (W : Γ ⊢V⦂ X) → VRed X W → CRed Y (V · W)
VRed {Γ} ⟨ X ⟩ V = {Y Z : Type} (K : Γ ⊢K⦂ Y ⊸ Z) (N : Γ ∷ X ⊢M⦂ Y) → ARed Y K N → SN (K aK (await V until N))

CRed {Γ} X M = {Y : Type} (K : Γ ⊢K⦂ X ⊸ Y) → KRed X K → SN (K aK M)

KRed {Γ} X K = (V : Γ ⊢V⦂ X) → VRed X V → SN (K aK (return V))
-- condition KRed2 holds trivially, since payload types are ground types which are base types

ARed {Γ} X {_} {Z} K N = (V : Γ ⊢V⦂ Z) → VRed Z V → SN (K aK (await ⟨ V ⟩ until N))

K'-↝ : {Γ : Ctx}
        {X Y Z : Type}
        (K : Γ ⊢K'⦂ Y ⊸ Z)
        (M : Γ ⊢M⦂ X)
        (T : Γ ⊢T⦂ X ⊸ Y)
        {L' : Γ ⊢M⦂ Z} →
        K aK' (T aT M) ↝↝ L' →
        ------------------------------
        Σ[ M' ∈ Γ ⊢M⦂ Y ]
        (K aK' M' ≡ L'
        ×
        (T aT M) ↝↝ M')
K'-↝ id _ (T-let _) r = _ , refl , r
K'-↝ id _ (T-op _ _) r = _ , refl , r
K'-↝ (T-let _ T∘ id) M (T-let _) (context-let r) = _ , refl , r
K'-↝ (T-let _ T∘ id) M (T-op _ _) (context-let r) = _ , refl , r
K'-↝ (T-let _ T∘ K'@(T-let _ T∘ _)) M T (context-let r) with K'-↝ K' M T r
... | _ , refl , r' = _ , refl , r'
K'-↝ (T-let _ T∘ K'@(T-op _ _ T∘ _)) M T (context-let r) with K'-↝ K' M T r
... | _ , refl , r' = _ , refl , r'
K'-↝ (T-op _ _ T∘ id) _ (T-let _) (context-↓ r) = _ , refl , r
K'-↝ (T-op _ _ T∘ id) _ (T-op _ _) (context-↓ r) = _ , refl , r
K'-↝ (T-op _ _ T∘ K'@(T-let _ T∘ _)) M T (context-↓ r) with K'-↝ K' M T r
... | _ , refl , r' = _ , refl , r'
K'-↝ (T-op _ _ T∘ K'@(T-op _ _ T∘ _)) M T (context-↓ r) with K'-↝ K' M T r
... | _ , refl , r' = _ , refl , r'

K-↝ : {Γ : Ctx}
        {X Y Z : Type}
        (K : Γ ⊢K⦂ Y ⊸ Z)
        (M : Γ ⊢M⦂ X)
        (T : Γ ⊢T⦂ X ⊸ Y)
        {L' : Γ ⊢M⦂ Z} →
        K aK (T aT M) ↝↝ L' →
        ------------------------------
        Σ[ M' ∈ Γ ⊢M⦂ Y ]
        (K aK M' ≡ L'
        ×
        (T aT M) ↝↝ M')
K-↝ K M T {L'} r with K'-↝ (to K) M T (subst (_↝↝ L') (to-app K (T aT M)) r)
... | M' , refl , r' = M' , to-app K M' , r'

KRed-∘t : {Γ : Ctx}
          {X Y Z : Type}  
          (K : Γ ⊢K⦂ Y ⊸ Z) →
          (N : Γ ∷ X ⊢M⦂ Y) →
          (V : Γ ⊢V⦂ X) →
          {L' : Γ ⊢M⦂ Z} →
          SN (K aK (N [ id-subst [ V ]s ]m)) →
          K aK (let= return V `in N) ↝↝ L' →
          ------------------------------------
          SN L'
KRed-∘t K N V app-sn r with K-↝ K (return V) (T-let N) r
... | _ , refl , let-return .V .N = app-sn

KRed-∘i : {Γ : Ctx}
          {X Y : Type}  
          (K : Γ ⊢K⦂ X ⊸ Y) →
          (op : Σₛ) →
          (W : Γ ⊢V⦂ ``(payload op)) →
          (V : Γ ⊢V⦂ X) →
          {L' : Γ ⊢M⦂ Y} →
          SN (K aK (return V)) →
          K aK (↓ op W (return V)) ↝↝ L' →
          ------------------------------------
          SN L'
KRed-∘i K op W V app-sn r with K-↝ K (return V) (T-op op W) r
... | _ , refl , ↓-return .W .V = app-sn

aK-↝↝ : {Γ : Ctx}
          {X Y : Type}
          (K : Γ ⊢K⦂ X ⊸ Y)
          {M N : Γ ⊢M⦂ X} →
          M ↝↝ N →
          ------------------
          K aK M ↝↝ K aK N
aK-↝↝ id r = r
aK-↝↝ (K ∘T T-let N) r = aK-↝↝ K (context-let r)
aK-↝↝ (K ∘T T-op op x) r = aK-↝↝ K (context-↓ r)

append-↑ : {Γ : Ctx}
           {X Y : Type}  
           (K : Γ ⊢K⦂ X ⊸ Y)
           (op : Σₛ)
           (W : Γ ⊢V⦂ ``(payload op))
           (M : Γ ⊢M⦂ X)
           {L' : Γ ⊢M⦂ Y} →
           SN (K aK M) →
           K aK (↑ op W M) ↝↝ L' →
           ---------------------------
           SN L'
append-↑ id op W M (sn f) (context-↑ r) = sn (λ r' → append-↑ id op W _ (f r) r')
append-↑ (K ∘T T) op W M app-sn r with K-↝ K (↑ op W M) T r
append-↑ (K ∘T T-let N) op W M app-sn r | _ , refl , let-↑ .W .M .N = sn (λ r' → append-↑ K op W (let= M `in N) app-sn r')
append-↑ (K ∘T T-let N) op W M (sn f) r | _ , refl , context-let (context-↑ r')
  = sn (λ r'' → append-↑ (K ∘T T-let N) op W _ (f (aK-↝↝ (K ∘T T-let N) r')) r'')
append-↑ (K ∘T T-op op' W') op W M app-sn r | _ , refl , ↓-↑ .W' .W .M = sn (λ r' → append-↑ K op W (↓ op' W' M) app-sn r')
append-↑ (K ∘T T-op op' W') op W M (sn f) r | _ , refl , context-↓ (context-↑ r')
  = sn λ r'' → append-↑ (K ∘T T-op op' W') op W _ (f (aK-↝↝ (K ∘T T-op op' W') r')) r''

append-↑-sn : {Γ : Ctx}
              {X Y : Type}  
              (K : Γ ⊢K⦂ X ⊸ Y)
              (op : Σₛ)
              (W : Γ ⊢V⦂ ``(payload op))
              (M : Γ ⊢M⦂ X) →
              SN (K aK M) →
              -------------------------
              SN (K aK (↑ op W M))
append-↑-sn K op W M app-sn = sn (λ r → append-↑ K op W M app-sn r)

append-await : {Γ : Ctx}
               {X Y Z : Type}  
               (K : Γ ⊢K⦂ Y ⊸ Z)
               {W : Γ ⊢V⦂ X}
               (N : Γ ∷ X ⊢M⦂ Y)
               {L' : Γ ⊢M⦂ Z} →
               SN (K aK (N [ id-subst [ W ]s ]m)) →
               K aK (await ⟨ W ⟩ until N) ↝↝ L' →
               ---------------------------
               SN L'
append-await id N app-sn (await-promise _ .N) = app-sn
append-await (K ∘T T-let N') N app-sn r with K-↝ K (await ⟨ _ ⟩ until N) (T-let N') r
... | _ , refl , context-let (await-promise _ .N) = app-sn
append-await (K ∘T T-op op' W') N app-sn r with K-↝ K (await ⟨ _ ⟩ until N) (T-op op' W') r
... | _ , refl , context-↓ (await-promise _ .N) = app-sn

sn-↝↝-lemma : {Γ Γ' : Ctx}
              {X : Type}
              {N N' : Γ ⊢M⦂ X}
              (s : Sub Γ Γ') →
              N ↝↝ N' →
              SN (N [ s ]m) →
              ---------------
              SN (N' [ s ]m)
sn-↝↝-lemma s r (sn snn) = snn (sub-↝↝ s r)

wk₁K : {Γ : Ctx} {X Y Z : Type} → Γ ⊢K⦂ X ⊸ Y → Γ ∷ Z ⊢K⦂ X ⊸ Y
wk₁K id = id
wk₁K (K ∘T T-let N) = (wk₁K K) ∘T T-let (M-rename (comp-ren exchange wk₁) N)
wk₁K (K ∘T T-op op V) = (wk₁K K) ∘T T-op op (V-rename wk₁ V)

sn-K-↑' : {Γ : Ctx}
           {X Y : Type}
           {op : Σₛ}
           {K : Γ ⊢K⦂ X ⊸ Y}
           {V : Γ ⊢V⦂ ``(payload op)}
           {M : Γ ⊢M⦂ X} →
           SN (K aK (↑ op V M)) →
           ---------------------
           SN (↑ op V (K aK M))
sn-K-↑' {K = id} s = s
sn-K-↑' {K = K ∘T T-let N} (sn f) = sn-K-↑' {K = K} (f (aK-↝↝ K (let-↑ _ _ N)))
sn-K-↑' {K = K ∘T T-op op' W} (sn f) = sn-K-↑' {K = K} (f (aK-↝↝ K (↓-↑ _ _ _)))

{-sn-K-↑ : {Γ : Ctx}
         {X Y : Type}
         {op : Σₛ}
         {K : Γ ⊢K⦂ X ⊸ Y}
         {V : Γ ⊢V⦂ ``(payload op)}
         {M : Γ ⊢M⦂ X} →
         SN (K aK (↑ op V M)) →
         ----------------------
         SN (K aK M)
sn-K-↑ {K = id} (sn f) = sn (λ z → sn-K-↑ {K = id} (f (context-↑ z)))
sn-K-↑ {K = K ∘T T-let N} (sn f) = sn-↑ (sn-K-↑' {K = K} (f (aK-↝↝ K (let-↑ _ _ _))))
sn-K-↑ {K = K ∘T T-op op W} (sn f) = sn-↑ (sn-K-↑' {K = K} (f (aK-↝↝ K (↓-↑ _ _ _))))
-}

rename-lemma-v : {Γ : Ctx}
                 {X Y : Type}
                 {W : Γ ⊢V⦂ X}
                 {V : Γ ⊢V⦂ Y} →
                 -----------------------------
                 V-rename wk₁ W [ id-subst [ V ]s ]v ≡ W
rename-lemma-v {W = W} {V = V} =
  begin
    V-rename wk₁ W [ id-subst [ V ]s ]v
  ≡⟨ commute-subst-rename-v {V = W} (λ {Hd → refl; (Tl x) → refl}) ⟩
    V-rename id-ren (W [ id-subst ]v)
  ≡⟨ ren-id-v ⟩
    W [ id-subst ]v
  ≡⟨ sub-id-v ⟩
    W
  ∎

rename-lemma-m : {Γ : Ctx}
                 {X Y : Type}
                 {M : Γ ∷ X ⊢M⦂ Y}
                 {V : Γ ⊢V⦂ X} →
                 -----------------------------
                 M-rename (comp-ren exchange wk₁) M [ lift (id-subst [ V ]s) ]m ≡ M
rename-lemma-m {M = M} {V = V} =
  begin 
    M-rename (comp-ren exchange wk₁) M [ lift (id-subst [ V ]s) ]m
  ≡⟨ commute-subst-rename-m {M = M} (λ {Hd → refl; (Tl x) → refl}) ⟩
    M-rename id-ren (M [ id-subst ]m)
  ≡⟨ ren-id-m ⟩
    M [ id-subst ]m
  ≡⟨ sub-id-m ⟩
    M
  ∎

append-promise : {Γ : Ctx}
                 {X Y Z : Type}  
                 (K : Γ ⊢K⦂ Y ⊸ Z)
                 (op : Σₛ)
                 (M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩)
                 (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                 ({V : Γ ⊢V⦂ ⟨ X ⟩} → VRed ⟨ X ⟩ V → SN (K aK (N [ id-subst [ V ]s ]m))) →
                 ({W : Γ ⊢V⦂ ``(payload op)} → CRed ⟨ X ⟩ (M [ id-subst [ W ]s ]m)) →
                 SN ((wk₁K K) aK N) →
                 {L' : Γ ⊢M⦂ Z} →
                 K aK (promise op ↦ M `in N) ↝↝ L' →
                 ---------------------------
                 SN L'

cred-await : {Γ : Ctx}
             {X Y : Type}
             (V : Γ ⊢V⦂ ⟨ X ⟩)
             (N : Γ ∷ X ⊢M⦂ Y) →
             VRed ⟨ X ⟩ V →
             ({W : Γ ⊢V⦂ X} → VRed X W → CRed Y (N [ id-subst [ W ]s ]m)) →
             -----------------
             CRed Y (await V until N)
cred-await V N VRedV f K KRedK
  = VRedV K N (λ W VRedW → sn (λ r → append-await K N ((f VRedW) K KRedK) r))

cred-let : {Γ : Ctx}
           {X Y : Type}  
           (M : Γ ⊢M⦂ X)
           (N : Γ ∷ X ⊢M⦂ Y) →
           CRed X M →
           ({W : Γ ⊢V⦂ X} → VRed X W → CRed Y (N [ id-subst [ W ]s ]m)) →
           -----------------------------
           CRed Y (let= M `in N)
cred-let M N CRedM f K KRedK
  = CRedM (K ∘T T-let N) (λ V VRedV → sn (λ r → KRed-∘t K N V (f VRedV K KRedK) r))

cred-↓ : {Γ : Ctx}
         {X : Type}  
         (M : Γ ⊢M⦂ X)
         (op : Σₛ) →
         (W : Γ ⊢V⦂ ``(payload op)) →
         CRed X M →
         -----------------------------
         CRed X (↓ op W M)
cred-↓ M op W CRedM K KRedK
  = CRedM (K ∘T T-op op W) (λ V VRedV → sn (λ r → KRed-∘i K op W V (KRedK V VRedV) r))

cred-↑ : {Γ : Ctx}
         {X : Type}  
         (M : Γ ⊢M⦂ X)   
         (op : Σₛ) → 
         (W : Γ ⊢V⦂ ``(payload op)) →
         CRed X M →
         ----------------------------- 
         CRed X (↑ op W M)          
cred-↑ M op W CRedM K KRedK = sn (λ r → append-↑ K op W M (CRedM K KRedK) r) 