open import AEff hiding (``_)
open import Types
open import Substitutions
open import Preservation
open import Finality

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

data _⊢K⦂_⊸_ (Γ : Ctx) : Type → Type → Set where

  id      : {X : Type} →
            ------------
            Γ ⊢K⦂ X ⊸ X
  _∘t_    : {X Y Z : Type} →
            Γ ⊢K⦂ Y ⊸ Z →
            Γ ∷ X ⊢M⦂ Y →
            ------------
            Γ ⊢K⦂ X ⊸ Z
  _∘i_⟨_⟩ : {X Y : Type} →
            Γ ⊢K⦂ X ⊸ Y →
            (op : Σₛ) →
            Γ ⊢V⦂ ``(payload op) →
            ------------
            Γ ⊢K⦂ X ⊸ Y

length  : {Γ : Ctx}
          {X Y : Type} →
          Γ ⊢K⦂ X ⊸ Y →
          ------------
          ℕ
length id = zero
length (K ∘t N) = suc (length K)
length (K ∘i op ⟨ V ⟩) = suc (length K)

infix 20 _a_

_a_ : {Γ : Ctx}
       {X Y : Type}
       (K : Γ ⊢K⦂ X ⊸ Y) →
       Γ ⊢M⦂ X →
       --------------
       Γ ⊢M⦂ Y
id a M = M
(K ∘t N) a M = K a (let= M `in N)
(K ∘i op ⟨ V ⟩) a M = K a (↓ op V M)

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
-- condition KRed2 holds trivially, since payload types are ground types which are base types

ARed {Γ} X {_} {Z} A N = {V : Γ ⊢V⦂ Z} → VRed Z V → SN (A a (await ⟨ V ⟩ until N))

K-↝ : {Γ : Ctx}
       {X Y Z : Type}
       (K : Γ ⊢K⦂ Y ⊸ Z)
       (M : Γ ⊢M⦂ X)
       (N : Γ ∷ X ⊢M⦂ Y)
       (L L' : Γ ⊢M⦂ Z) →
       K a (let= M `in N) ≡ L →
       L ↝↝ L' →
       ------------------------------
       Σ[ M' ∈ Γ ⊢M⦂ Y ]
       (K a M' ≡ L'
       ×
       (let= M `in N) ↝↝ M')

       
KRed-∘t : {Γ : Ctx}
          {X Y Z : Type} 
          (K : Γ ⊢K⦂ Y ⊸ Z) →
          (N : Γ ∷ X ⊢M⦂ Y) →
          ({W : Γ ⊢V⦂ X} → VRed X W → SN (K a (N [ id-subst [ W ]s ]m))) →
          KRed Y K →   
          -------------------  
          KRed X (K ∘t N) 