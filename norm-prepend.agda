open import Data.List using (List; []) renaming (_∷_ to _∷₁_)

open import AEff hiding (``_; [])
open import Types
open import Substitutions
open import Preservation
open import Finality

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.Product
open import Data.Sum
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality hiding ([_])

data _⊢K⦂_⊸_ (Γ : Ctx) : Type → Type → Set where

  [-]              : {X : Type} → 
                     -------------
                     Γ ⊢K⦂ X ⊸ X

  let=_`in_        : {X Y Z : Type} →
                     Γ ⊢K⦂ X ⊸ Y →
                     Γ ∷ Y ⊢M⦂ Z →
                     ------------------------
                     Γ ⊢K⦂ X ⊸ Z

  ↓                : {X Y : Type}
                     (op : Σₛ) →
                     Γ ⊢V⦂ ``(payload op) →
                     Γ ⊢K⦂ X ⊸ Y →
                     ---------------------------
                     Γ ⊢K⦂ X ⊸ Y


_∘t_ : {Γ : Ctx}
       {X Y Z : Type}
       (K : Γ ⊢K⦂ Y ⊸ Z) →
       Γ ∷ X ⊢M⦂ Y →
       -------------------------------
       Γ ⊢K⦂ X ⊸ Z
[-] ∘t N = let= [-] `in N 
(let= K `in N') ∘t N = let= (K ∘t N) `in N'
↓ op V K ∘t N = ↓ op V (K ∘t N)

_∘i_⟨_⟩ : {Γ : Ctx}
          {X Y : Type}
          (K : Γ ⊢K⦂ X ⊸ Y)
          (op : Σₛ) →
          Γ ⊢V⦂ ``(payload op) →
          -------------------------
          Γ ⊢K⦂ X ⊸ Y
[-] ∘i op ⟨ V ⟩ = ↓ op V [-] 
(let= K `in N') ∘i op ⟨ V ⟩ = let= (K ∘i op ⟨ V ⟩) `in N'
(↓ op' V' K) ∘i op ⟨ V ⟩ = ↓ op' V' (K ∘i op ⟨ V ⟩)

length  : {Γ : Ctx}
          {X Y : Type} →
          Γ ⊢K⦂ X ⊸ Y →
          ------------
          ℕ
length [-] = zero 
length (let= K `in x) = suc (length K)
length (↓ op x K) = suc (length K)

infix 20 _a_

_a_ : {Γ : Ctx}
       {X Y : Type}
       (K : Γ ⊢K⦂ X ⊸ Y) →
       Γ ⊢M⦂ X →
       --------------
       Γ ⊢M⦂ Y
[-] a M = M 
(let= K `in N) a M = let= (K a M) `in N
↓ op V K a M = ↓ op V (K a M)

data SN_ : {Γ : Ctx} {X : Type} → (Γ ⊢M⦂ X) → Set where
  sn : {Γ : Ctx}
       {X : Type}
       {M : Γ ⊢M⦂ X} →
       ({N : Γ ⊢M⦂ X} → M ↝ N → SN N) →
       ----------------------------------
       SN M

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
VRed {Γ} (X ⇒ Y) V = {W : Γ ⊢V⦂ X} → VRed X W → CRed Y (V · W)
VRed {Γ} ⟨ X ⟩ V = {Y Z : Type} {A : Γ ⊢K⦂ Y ⊸ Z} {N : Γ ∷ X ⊢M⦂ Y} → ARed Y A N → SN (A a (await V until N))

CRed {Γ} X M = {Y : Type} {K : Γ ⊢K⦂ X ⊸ Y} → KRed X K → SN (K a M)

KRed {Γ} X K = {V : Γ ⊢V⦂ X} → VRed X V → SN (K a (return V))

ARed {Γ} X {_} {Z} A N = {V : Γ ⊢V⦂ Z} → VRed Z V → SN (A a (await ⟨ V ⟩ until N))

K-↝ : {Γ : Ctx}
       {X Y Z : Type}
       (K : Γ ⊢K⦂ Y ⊸ Z)
       (V : Γ ⊢V⦂ X)
       (N : Γ ∷ X ⊢M⦂ Y)
       (L L' : Γ ⊢M⦂ Z) →
       K a (let= (return V) `in N) ≡ L →
       L ↝↝ L' →
       ------------------------------
       L' ≡ (K a (N [ id-subst [ V ]s ]m))
K-↝ [-] V N L L' refl (let-return .V .N) = refl
K-↝ (let= K `in x) V N L L' ≡L r = {!   !}
K-↝ (↓ op x K) V N L L' ≡L r = {!   !}