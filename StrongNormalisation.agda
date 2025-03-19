open import AEff
open import Types
open import Finality

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product

data SN : {Γ : Ctx} {X : Type} → Γ ⊢M⦂ X → Set where
  sn : {Γ : Ctx}
       {X : Type}
       {M : Γ ⊢M⦂ X} →
       ({N : Γ ⊢M⦂ X} → M ↝↝ N → SN N) →
       --------------------------------
       SN M

{-data _≺_ : {Γ : Ctx} {X : Type} {M N : Γ ⊢M⦂ X} → SN M → SN N → Set where
  ≺-cons : {Γ : Ctx}
           {X : Type}
           {M N : Γ ⊢M⦂ X}
           (f : {M' : Γ ⊢M⦂ X} → M ↝↝ M' → SN M')
           (r : M ↝↝ N) →
           -------------
           f r ≺ (sn f)

data _l-<_ : {Γ : Ctx} {X : Type} → Σ[ M ∈ Γ ⊢M⦂ X ] SN M → Σ[ N ∈ Γ ⊢M⦂ X ] SN N → Set where
  fst-< : {Γ : Ctx}
          {X : Type}
          {M N : Γ ⊢M⦂ X}
          (s : SN M)
          (r : M ↝↝ N)
          (f : {M' : Γ ⊢M⦂ X} → M ↝↝ M' → SN M') →
          -----------------
          (N , (f r)) l-< (M , s)
-}