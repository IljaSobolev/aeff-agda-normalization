open import AEff renaming (``_ to ```_)
open import Types
open import Substitutions
open import Renamings
open import Preservation
open import Finality

open import SubstitutionProperties
open import StrongNormalisation
open import Continuations

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; subst; subst₂; sym; trans)
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

append-let : {Γ : Ctx}
             {X Y Z : Type}  
             (K : Γ ⊢K⦂ Y ⊸ Z) →
             (N : Γ ∷ X ⊢M⦂ Y) →
             (V : Γ ⊢V⦂ X) →
             {L' : Γ ⊢M⦂ Z} →
             SN (K aK (N [ id-subst [ V ]s ]m)) →
             K `aK (let= return V `in N) `↝↝ L' →
             ------------------------------------
             SN L'
append-let K N V app-sn (`id (let-return .V .N)) = app-sn
append-let K N V app-sn (`aK {T = T-let N'} (context-let (let-return .V .N))) = app-sn
append-let K N V app-sn (`aK {T = T-op op' V'} (context-↓ (let-return .V .N))) = app-sn

kred-let : {Γ : Ctx}
           {X Y Z : Type}  
           (K : Γ ⊢K⦂ Y ⊸ Z) →
           (N : Γ ∷ X ⊢M⦂ Y) →
           ({V : Γ ⊢V⦂ X} → VRed X V → SN (K aK (N [ id-subst [ V ]s ]m))) →
           ---------------------
           KRed X (K ∘T T-let N)
kred-let K N f V VRedV = sn (λ {r' → append-let K N V (f VRedV) (aK→`aK r')})

append-↓ : {Γ : Ctx}
           {X Y : Type}  
           (K : Γ ⊢K⦂ X ⊸ Y) →
           (op : Σₛ) →
           (W : Γ ⊢V⦂ ``(payload op)) →
           (V : Γ ⊢V⦂ X) →
           {L' : Γ ⊢M⦂ Y} →
           SN (K aK (return V)) →
           K `aK (↓ op W (return V)) `↝↝ L' →
           ------------------------------------
           SN L'
append-↓ K op W V app-sn (`id (↓-return .W .V)) = app-sn
append-↓ K op W V app-sn (`aK {T = T-let N'} (context-let (↓-return .W .V))) = app-sn
append-↓ K op W V app-sn (`aK {T = T-op op' V'} (context-↓ (↓-return .W .V))) = app-sn

append-↑ : {Γ : Ctx}
           {X Y : Type}  
           (K : Γ ⊢K⦂ X ⊸ Y)
           (op : Σₛ)
           (W : Γ ⊢V⦂ ``(payload op))
           (M : Γ ⊢M⦂ X)
           {L' : Γ ⊢M⦂ Y} →
           SN (K aK M) →
           K `aK (↑ op W M) `↝↝ L' →
           ---------------------------
           SN L'
append-↑ K op W M (sn f) (`id (context-↑ r)) = sn-↑-i (f r)
append-↑ (K ∘T T-let N') op W M app-sn (`aK {T = T-let N'} (let-↑ .W .M .N'))
  = sn (λ r' → append-↑ K op W (let= M `in N') app-sn (aK→`aK r'))
append-↑ K op W M (sn f) (`aK {T = T-let N'} (context-let (context-↑ r)))
  = sn (λ r' → append-↑ K op W _ (f (aK-↝↝ K r)) (aK→`aK r'))
append-↑ (K ∘T T-op op' V') op W M app-sn (`aK {T = T-op op' V'} (↓-↑ .V' .W .M))
  = sn (λ r' → append-↑ K op W (↓ op' V' M) app-sn (aK→`aK r'))
append-↑ K op W M (sn f) (`aK {T = T-op op' V'} (context-↓ (context-↑ r)))
  = sn (λ r' → append-↑ K op W _ (f (aK-↝↝ K r)) (aK→`aK r'))

append-↑-sn : {Γ : Ctx}
              {X Y : Type}  
              (K : Γ ⊢K⦂ X ⊸ Y)
              (op : Σₛ)
              (W : Γ ⊢V⦂ ``(payload op))
              (M : Γ ⊢M⦂ X) →
              SN (K aK M) →
              -------------------------
              SN (K aK (↑ op W M))
append-↑-sn K op W M app-sn = sn (λ r → append-↑ K op W M app-sn (aK→`aK r))

append-await : {Γ : Ctx}
               {X Y Z : Type}  
               (K : Γ ⊢K⦂ Y ⊸ Z)
               {W : Γ ⊢V⦂ X}
               (N : Γ ∷ X ⊢M⦂ Y)
               {L' : Γ ⊢M⦂ Z} →
               SN (K aK (N [ id-subst [ W ]s ]m)) →
               K `aK (await ⟨ W ⟩ until N) `↝↝ L' →
               ---------------------------
               SN L'
append-await id N app-sn (`id (await-promise _ _)) = app-sn
append-await (K ∘T T-let N') N app-sn (`aK (context-let (await-promise _ _))) = app-sn
append-await (K ∘T T-op op V) N app-sn (`aK (context-↓ (await-promise _ _))) = app-sn

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

sn-K-↑ : {Γ : Ctx}
         {X Y : Type}
         {op : Σₛ}
         {K : Γ ⊢K⦂ X ⊸ Y}
         {V : Γ ⊢V⦂ ``(payload op)}
         {M : Γ ⊢M⦂ X} →
         SN (K aK (↑ op V M)) →
         ----------------------
         SN (K aK M)
sn-K-↑ {K = id} (sn f) = sn (λ z → sn-K-↑ {K = id} (f (context-↑ z)))
sn-K-↑ {K = K ∘T T-let N} (sn f) = sn-↑-e (sn-K-↑' {K = K} (f (aK-↝↝ K (let-↑ _ _ _))))
sn-K-↑ {K = K ∘T T-op op W} (sn f) = sn-↑-e (sn-K-↑' {K = K} (f (aK-↝↝ K (↓-↑ _ _ _))))

sni-K-↑' : {Γ : Ctx}
           {X Y : Type}
           {m : ℕ}
           {op : Σₛ}
           {K : Γ ⊢K⦂ X ⊸ Y}
           {V : Γ ⊢V⦂ ``(payload op)}
           {M : Γ ⊢M⦂ X} →
           SNi m (K aK (↑ op V M)) →
           ---------------------
           SNi m (↑ op V (K aK M))
sni-K-↑' {K = id} s = s
sni-K-↑' {K = K ∘T T-let N} (sni f) = sni-K-↑' {K = K} (sni-suc (f (aK-↝↝ K (let-↑ _ _ _))))
sni-K-↑' {K = K ∘T T-op op' W} (sni f) = sni-K-↑' {K = K} (sni-suc (f (aK-↝↝ K (↓-↑ _ _ _))))

sni-K-↑ : {Γ : Ctx}
          {X Y : Type}
          {m : ℕ}
          {op : Σₛ}
          {K : Γ ⊢K⦂ X ⊸ Y}
          {V : Γ ⊢V⦂ ``(payload op)}
          {M : Γ ⊢M⦂ X} →
          SNi m (K aK (↑ op V M)) →
          ----------------------
          SNi m (K aK M)
sni-K-↑ {K = id} (sni f) = sni (λ z → sni-K-↑ {K = id} (f (context-↑ z)))
sni-K-↑ {K = K ∘T T-let N} (sni f) = sni-↑-e (sni-K-↑' {K = K} (sni-suc (f (aK-↝↝ K (let-↑ _ _ _)))))
sni-K-↑ {K = K ∘T T-op op W} (sni f) = sni-↑-e (sni-K-↑' {K = K} (sni-suc (f (aK-↝↝ K (↓-↑ _ _ _)))))

rename-lemma-v : {Γ : Ctx}
                 {X Y : Type}
                 {W : Γ ⊢V⦂ X}
                 {V : Γ ⊢V⦂ Y} →
                 -----------------------------
                 W ≡ V-rename wk₁ W [ id-subst [ V ]s ]v
rename-lemma-v {W = W} {V = V} = sym (
  begin
    V-rename wk₁ W [ id-subst [ V ]s ]v
  ≡⟨ commute-subst-rename-v {V = W} (λ {Hd → refl; (Tl x) → refl}) ⟩
    V-rename id-ren (W [ id-subst ]v)
  ≡⟨ ren-id-v ⟩
    W [ id-subst ]v
  ≡⟨ sub-id-v ⟩
    W
  ∎
  )

rename-lemma-m : {Γ : Ctx}
                 {X Y Z : Type}
                 {M : Γ ∷ X ⊢M⦂ Y}
                 {V : Γ ⊢V⦂ Z} →
                 -----------------------------
                 M ≡ M-rename (comp-ren exchange wk₁) M [ lift (id-subst [ V ]s) ]m
rename-lemma-m {M = M} {V = V} = sym (
  begin 
    M-rename (comp-ren exchange wk₁) M [ lift (id-subst [ V ]s) ]m
  ≡⟨ commute-subst-rename-m {M = M} (λ {Hd → refl; (Tl x) → refl}) ⟩
    M-rename id-ren (M [ id-subst ]m)
  ≡⟨ ren-id-m ⟩
    M [ id-subst ]m
  ≡⟨ sub-id-m ⟩
    M
  ∎
  )

rename-lemma-m' : {Γ : Ctx}
                  {X Y : Type}
                  {M : Γ ∷ X ⊢M⦂ Y} →
                  -----------------------------
                  M ≡ M-rename (comp-ren exchange wk₁) M [ id-subst [ ` Hd ]s ]m
rename-lemma-m' {M = M} = sym (
  begin
    M-rename (comp-ren exchange wk₁) M [ id-subst [ ` Hd ]s ]m
  ≡⟨ commute-subst-rename-m {M = M} {s = id-subst} {rΔ = id-ren} (λ {Hd → refl; (Tl x) → refl}) ⟩
    M-rename id-ren (M [ id-subst ]m)
  ≡⟨ ren-id-m ⟩
    M [ id-subst ]m
  ≡⟨ sub-id-m ⟩
    M
  ∎
  )

append-promise : {Γ : Ctx}
                 {X Y Z : Type}  
                 {m : ℕ}
                 (K : Γ ⊢K⦂ Y ⊸ Z)
                 (op : Σₛ)
                 (M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩)
                 (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                 ({V : Γ ⊢V⦂ ⟨ X ⟩} → VRed ⟨ X ⟩ V → SN (K aK (N [ id-subst [ V ]s ]m))) →
                 ({W : Γ ⊢V⦂ ``(payload op)} → CRed ⟨ X ⟩ (M [ id-subst [ W ]s ]m)) →
                 SNi m (K aK (N [ id-subst [ ★ ]s ]m)) →
                 {L' : Γ ⊢M⦂ Z} →
                 K `aK (promise op ↦ M `in N) `↝↝ L' →
                 ---------------------------
                 SN L'
append-promise K op M N f g app-sni (`id (promise-↑ V .M N'))
  = sn-↑-i (sn (λ r' → append-promise id op M N' (λ VRedV → sn-↑-e (f VRedV)) g (sni-↑-e app-sni) (aK→`aK r')))
append-promise K op M N f g (sni h) (`id (context-promise r))
  = sn (λ r' → append-promise id op M _ (λ VRedV → (sn-decr (f VRedV)) (sub-↝↝ (id-subst [ _ ]s) r))
      g (h (sub-↝↝ (id-subst [ ★ ]s) r)) (aK→`aK r'))
append-promise K'@(K ∘T T-let N') op M N f g app-sni (`aK {T = T-let N'} (let-promise .M .N .N'))
  = sn (λ r' → append-promise K op M _
      (λ {V} VRedV → subst (λ z → SN (K aK (let= _ `in z))) rename-lemma-m (f VRedV))
      g (subst (λ z → SNi _ (K aK (let= N [ id-subst [ ★ ]s ]m `in z))) rename-lemma-m app-sni) (aK→`aK r'))
append-promise K'@(K ∘T T-let N') op M N f g (sni h) (`aK {T = T-let N'} (context-let (promise-↑ {op' = op'} V .M N₁)))
  = append-↑-sn K' op' (strengthen-val V) (promise op ↦ M `in N₁)
      (sn (λ r' → append-promise K' op M N₁ (λ VRedV → sn-K-↑ {K = K'} (f VRedV)) g (sni-K-↑ {K = K ∘T _} (sni h)) (aK→`aK r')))
append-promise K'@(K ∘T T-let N') op M N f g (sni h) (`aK {T = T-let N'} (context-let (context-promise r)))
  = sn (λ r' → append-promise K' op M _
      (λ VRedV → (sn-decr (f VRedV)) (aK-↝↝ (K ∘T _) (sub-↝↝ (id-subst [ _ ]s) r)) )
       g (h (aK-↝↝ (K ∘T _) (sub-↝↝ (id-subst [ ★ ]s) r))) (aK→`aK r'))
append-promise K'@(K ∘T T-op op' V') op M N f g app-sni (`aK {T = T-op op' V'} (↓-promise-op .V' .M .N))
  = ((g {V'}) (K ∘T T-let (↓ op' (V-rename wk₁ V') (M-rename (comp-ren exchange wk₁) N [ id-subst [ ` Hd ]s ]m)))
      (kred-let K (↓ op' (V-rename wk₁ V') (M-rename (comp-ren exchange wk₁) N [ id-subst [ ` Hd ]s ]m))
        (λ VRedV → subst₂ (λ z w → SN (K aK ↓ op' z w)) rename-lemma-v (cong (λ u → u [ id-subst [ _ ]s ]m) rename-lemma-m') (f VRedV))))
append-promise K'@(K ∘T T-op op' V') op M N f g app-sni (`aK {T = T-op op' V'} (↓-promise-op' p .V' .M .N))
  = sn (λ r' → append-promise K op M _
      (λ {V} VRedV → subst (λ z → SN (K aK ↓ op' z _)) rename-lemma-v (f VRedV))
      g (subst (λ z → SNi _ (K aK ↓ op' z (N [ id-subst [ ★ ]s ]m))) rename-lemma-v app-sni) (aK→`aK r'))
append-promise K'@(K ∘T T-op op' V') op M N f g (sni h) (`aK {T = T-op op' V'} (context-↓ (promise-↑ {op' = op''} V .M N₁)))
  = append-↑-sn K' op'' (strengthen-val V) (promise op ↦ M `in N₁)
      (sn (λ r' → append-promise K' op M N₁ (λ VRedV → sn-K-↑ {K = K'} (f VRedV)) g (sni-K-↑ {K = K ∘T _} (sni h)) (aK→`aK r')))
append-promise K'@(K ∘T T-op op' V') op M N f g (sni h) (`aK {T = T-op op' V'} (context-↓ (context-promise r)))
  = sn (λ r' → append-promise K' op M _
      (λ VRedV → (sn-decr (f VRedV)) (aK-↝↝ (K ∘T _) (sub-↝↝ (id-subst [ _ ]s) r)))
      g (h (aK-↝↝ (K ∘T _) (sub-↝↝ (id-subst [ ★ ]s) r))) (aK→`aK r'))

cred-await : {Γ : Ctx}
             {X Y : Type}
             (V : Γ ⊢V⦂ ⟨ X ⟩)
             (N : Γ ∷ X ⊢M⦂ Y) →
             VRed ⟨ X ⟩ V →
             ({W : Γ ⊢V⦂ X} → VRed X W → CRed Y (N [ id-subst [ W ]s ]m)) →
             -----------------
             CRed Y (await V until N)
cred-await V N VRedV f K KRedK
  = VRedV K N (λ W VRedW → sn (λ r' → append-await K N (f VRedW K KRedK) (aK→`aK r')))

var-app-sn : {Γ : Ctx}
             {X Y Z : Type}
             {K : Γ ⊢K⦂ X ⊸ Y}
             {V : Γ ⊢V⦂ Z}
             {x : Z ⇒ X ∈ Γ} →
             {L' : Γ ⊢M⦂ Y} →
             K `aK (` x) · V `↝↝ L' →
             ------------------------
             SN L'
var-app-sn (`aK {T = T-let N} (context-let ()))
var-app-sn (`aK {T = T-op op V} (context-↓ ()))

var-await-sn : {Γ : Ctx}
               {X Y Z : Type}
               {K : Γ ⊢K⦂ X ⊸ Y}
               {N : Γ ∷ Z ⊢M⦂ X}
               {x : ⟨ Z ⟩ ∈ Γ} →
               {L' : Γ ⊢M⦂ Y} →
               K `aK (await ` x until N) `↝↝ L' →
               ----------------------------------
               SN L'
var-await-sn (`aK {T = T-let N} (context-let ()))
var-await-sn (`aK {T = T-op op V} (context-↓ ()))

★-await-sn : {Γ : Ctx}
             {X Y Z : Type}
             {K : Γ ⊢K⦂ X ⊸ Y}
             {N : Γ ∷ Z ⊢M⦂ X}
             {L' : Γ ⊢M⦂ Y} →
             K `aK (await ★ until N) `↝↝ L' →
             ----------------------------------
             SN L'
★-await-sn (`aK {T = T-let N} (context-let ()))
★-await-sn (`aK {T = T-op op V} (context-↓ ()))

vred-var : {Γ : Ctx}
           {X : Type}
           (x : X ∈ Γ) →
           -------------
           VRed X (` x)
vred-var {X = `` c} x = tt
vred-var {X = X ⇒ Y} x V VRedV K KRedK = sn (λ r' → var-app-sn {K = K} (aK→`aK r'))
vred-var {X = ⟨ X ⟩} x K N ARedKN = sn (λ r' → var-await-sn {K = K} (aK→`aK r'))

vred-★ : {Γ : Ctx}
         {X : Type} →
         VRed {Γ} ⟨ X ⟩ ★
vred-★ K N ARedKN = sn (λ r' → ★-await-sn {K = K} (aK→`aK r'))

lam-abs-sn : {Γ : Ctx}
             {X Y Z : Type}
             {K : Γ ⊢K⦂ X ⊸ Y}
             {V : Γ ⊢V⦂ Z}
             {M : Γ ∷ Z ⊢M⦂ X} →
             {L' : Γ ⊢M⦂ Y} →
             SN (K aK (M [ id-subst [ V ]s ]m)) →
             K `aK (ƛ M) · V `↝↝ L' →
             ------------------------
             SN L'
lam-abs-sn s (`id (apply _ _)) = s
lam-abs-sn s (`aK {T = T-let N} (context-let (apply _ _))) = s
lam-abs-sn s (`aK {T = T-op op V} (context-↓ (apply _ _))) = s

vred-abs : {Γ : Ctx}
           {X Y : Type}
           {M : Γ ∷ X ⊢M⦂ Y} →
           ({V : Γ ⊢V⦂ X} → VRed X V → CRed Y (M [ id-subst [ V ]s ]m)) →
           ------------------
           VRed (X ⇒ Y) (ƛ M)
vred-abs f V VRedV K KRedK = sn (λ r' → lam-abs-sn {K = K} (f VRedV K KRedK) (aK→`aK r'))

cred-promise : {Γ : Ctx}
               {X Y : Type}
               {op : Σₛ}
               {M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩}
               {N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y} →
               ({V : Γ ⊢V⦂ ⟨ X ⟩} → VRed ⟨ X ⟩ V → CRed Y (N [ id-subst [ V ]s ]m)) →
               ({W : Γ ⊢V⦂ ``(payload op)} → CRed ⟨ X ⟩ (M [ id-subst [ W ]s ]m)) →
               -----------------------------
               CRed Y (promise op ↦ M `in N)
cred-promise {op = op} {M = M} {N = N} f g K KRedK
  = sn (λ r' → append-promise K op M N (λ {W} VRedW → f VRedW K KRedK) g (sn→sni (f vred-★ K KRedK)) (aK→`aK r'))

cred-let : {Γ : Ctx}
           {X Y : Type}  
           (M : Γ ⊢M⦂ X)
           (N : Γ ∷ X ⊢M⦂ Y) →
           CRed X M →
           ({V : Γ ⊢V⦂ X} → VRed X V → CRed Y (N [ id-subst [ V ]s ]m)) →
           -----------------------------
           CRed Y (let= M `in N)
cred-let M N CRedM f K KRedK
  = CRedM (K ∘T T-let N) (λ V VRedV → sn (λ r → append-let K N V (f VRedV K KRedK) (aK→`aK r)))

cred-↓ : {Γ : Ctx}
         {X : Type}  
         (M : Γ ⊢M⦂ X)
         (op : Σₛ) →
         (W : Γ ⊢V⦂ ``(payload op)) →
         CRed X M →
         -----------------------------
         CRed X (↓ op W M)
cred-↓ M op W CRedM K KRedK
  = CRedM (K ∘T T-op op W) (λ V VRedV → sn (λ r' → append-↓ K op W V (KRedK V VRedV) (aK→`aK r')))

cred-↑ : {Γ : Ctx}
         {X : Type}  
         (M : Γ ⊢M⦂ X)    
         (op : Σₛ) → 
         (W : Γ ⊢V⦂ ``(payload op)) →
         CRed X M →
         -----------------------------   
         CRed X (↑ op W M)                        
cred-↑ M op W CRedM K KRedK = sn (λ r → append-↑ K op W M (CRedM K KRedK) (aK→`aK r))

SubRed : {Γ Γ' : Ctx} (s : Sub Γ Γ') → Set
SubRed {Γ} s = {X : Type} (x : X ∈ Γ) → VRed X (s x)

subred-⨟ : {Γ Γ' : Ctx}
           {X : Type}
           {s : Sub Γ Γ'} →
           SubRed s →
           {V : Γ' ⊢V⦂ X} →
           VRed X V →
           -----------------------------------
           SubRed (lift s ⨟ (id-subst [ V ]s))
subred-⨟ sred VRedV Hd = VRedV
subred-⨟ {s = s} sred {V} VRedV (Tl x) rewrite sym (rename-lemma-v {W = s x} {V = V}) = sred x

cred-⨟ : {Γ Γ' : Ctx}
         {X Y : Type}
         {s : Sub Γ Γ'} →
         SubRed s →
         {V : Γ' ⊢V⦂ X} →
         VRed X V →
         (N : Γ ∷ X ⊢M⦂ Y) →
         ({Γ'' : Ctx} {s' : Sub (Γ ∷ X) Γ''} → SubRed s' → CRed Y (N [ s' ]m)) →
         ---------------------------------------------
         CRed Y ((N [ lift s ]m) [ id-subst [ V ]s ]m)
cred-⨟ {s = s} sred {V} VRedV N f K KRedK
  rewrite sub-sub-m {s = lift s} {s' = id-subst [ V ]s} N = f (subred-⨟ sred VRedV) K KRedK

fundamental-v : {Γ Γ' : Ctx}
                {X : Type}
                (V : Γ ⊢V⦂ X) →
                (s : Sub Γ Γ') →
                SubRed s →
                -----------------
                VRed X (V [ s ]v)

fundamental-m : {Γ Γ' : Ctx}
                {X : Type}
                (M : Γ ⊢M⦂ X) →
                (s : Sub Γ Γ') →
                SubRed s →
                -----------------
                CRed X (M [ s ]m)

fundamental-v (` x) s sred = sred x
fundamental-v (``` c) s sred = tt
fundamental-v (ƛ M) s sred
  = vred-abs (λ {V} VRedV K KRedK →
      subst (λ z → SN (K aK z)) (sym (sub-sub-m M))
        (fundamental-m M (lift s ⨟ (id-subst [ V ]s)) (subred-⨟ sred VRedV) K KRedK))
fundamental-v ⟨ V ⟩ s sred K N ARedKN = ARedKN (V [ s ]v) (fundamental-v V s sred)
fundamental-v ★ s sred = vred-★

fundamental-m (return V) s sred K KRedK = KRedK (V [ s ]v) (fundamental-v V s sred)
fundamental-m (let= M `in N) s sred
  = cred-let (M [ s ]m) (N [ lift s ]m)
      (fundamental-m M s sred)
      (λ VRedV → cred-⨟ sred VRedV N (fundamental-m N _))
fundamental-m (V · W) s sred = fundamental-v V s sred (W [ s ]v) (fundamental-v W s sred)
fundamental-m (↑ op V M) s sred = cred-↑ (M [ s ]m) op (V [ s ]v) (fundamental-m M s sred)
fundamental-m (↓ op V M) s sred = cred-↓ (M [ s ]m) op (V [ s ]v) (fundamental-m M s sred)
fundamental-m (promise op ↦ M `in N) s sred
  = cred-promise
      (λ {V} VRedV → cred-⨟ sred (λ {Y} {Z} → VRedV) N (fundamental-m N _))
      (cred-⨟ sred tt M (fundamental-m M _))
fundamental-m (await V until M) s sred
  = cred-await (V [ s ]v) (M [ lift s ]m)
      (fundamental-v V s sred)
      (λ VRedW → cred-⨟ sred VRedW M (fundamental-m M _))

cred→sn : {Γ : Ctx}
          {X : Type}  
          {M : Γ ⊢M⦂ X} →
          CRed X M →
          ------------
          SN M
cred→sn CRedM = CRedM id (λ V VRedV → sn (λ ()))

all-terms-red : {Γ : Ctx}
                {X : Type}
                (M : Γ ⊢M⦂ X) →
                --------------
                CRed X M
all-terms-red M rewrite sym (sub-id-m {M = M}) = fundamental-m M id-subst vred-var

all-terms-sn : {Γ : Ctx}
               {X : Type}
               (M : Γ ⊢M⦂ X) →
               --------------
               SN M
all-terms-sn M = cred→sn (all-terms-red M)