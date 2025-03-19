open import AEff
open import Types

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

data _⊢T⦂_⊸_ (Γ : Ctx) : Type → Type → Set where
  
  T-let : {X Y : Type}
          (N : Γ ∷ X ⊢M⦂ Y) →
          ------------------
          Γ ⊢T⦂ X ⊸ Y

  T-op  : {X : Type}
          (op : Σₛ) →
          Γ ⊢V⦂ ``(payload op) →
          ------------------
          Γ ⊢T⦂ X ⊸ X

data _⊢K⦂_⊸_ (Γ : Ctx) : Type → Type → Set where

  id      : {X : Type} →
            ------------
            Γ ⊢K⦂ X ⊸ X

  _∘T_    : {X Y Z : Type} →
            Γ ⊢K⦂ Y ⊸ Z →
            Γ ⊢T⦂ X ⊸ Y →
            ------------
            Γ ⊢K⦂ X ⊸ Z

data _⊢K'⦂_⊸_ (Γ : Ctx) : Type → Type → Set where

  id      : {X : Type} →
            ------------
            Γ ⊢K'⦂ X ⊸ X

  _T∘_    : {X Y Z : Type} →
            Γ ⊢T⦂ Y ⊸ Z →
            Γ ⊢K'⦂ X ⊸ Y →
            ------------
            Γ ⊢K'⦂ X ⊸ Z

_∘T'_ : {Γ : Ctx}
        {X Y Z : Type} →
        Γ ⊢K'⦂ Y ⊸ Z →
        Γ ⊢T⦂ X ⊸ Y →
        --------------
        Γ ⊢K'⦂ X ⊸ Z
id ∘T' T = T T∘ id
(T' T∘ K) ∘T' T = T' T∘ (K ∘T' T)

_T∘'_ : {Γ : Ctx}
        {X Y Z : Type} →
        Γ ⊢T⦂ Y ⊸ Z →
        Γ ⊢K⦂ X ⊸ Y →
        --------------
        Γ ⊢K⦂ X ⊸ Z
T T∘' id = id ∘T T
T T∘' (K' ∘T T') = (T T∘' K') ∘T T'

from : {Γ : Ctx}
     {X Y : Type} →
     Γ ⊢K'⦂ X ⊸ Y →
     --------------
     Γ ⊢K⦂ X ⊸ Y
from id = id
from (T T∘ K) = T T∘' (from K)

to : {Γ : Ctx}
     {X Y : Type} →
     Γ ⊢K⦂ X ⊸ Y →
     --------------
     Γ ⊢K'⦂ X ⊸ Y
to id = id
to (K ∘T T) = (to K) ∘T' T

infix 20 _aT_
infix 20 _aK_

_aT_ : {Γ : Ctx}
      {X Y : Type} →
      Γ ⊢T⦂ X ⊸ Y →
      Γ ⊢M⦂ X →
      ------------
      Γ ⊢M⦂ Y
T-let N aT M = let= M `in N
T-op op V aT M = ↓ op V M

_aK_ : {Γ : Ctx}
       {X Y : Type} →
       Γ ⊢K⦂ X ⊸ Y →
       Γ ⊢M⦂ X →
       -------------------
       Γ ⊢M⦂ Y
id aK M = M
(K ∘T T) aK M = K aK (T aT M)

_aK'_ : {Γ : Ctx}
       {X Y : Type} →
       Γ ⊢K'⦂ X ⊸ Y →
       Γ ⊢M⦂ X →
       -------------------
       Γ ⊢M⦂ Y
id aK' M = M
(T T∘ K) aK' M = T aT (K aK' M)

∘T'-app : {Γ : Ctx}
     {X Y Z : Type} →
     (K : Γ ⊢K'⦂ Y ⊸ Z) →
     (T : Γ ⊢T⦂ X ⊸ Y) →
     (M : Γ ⊢M⦂ X) →
     ---------------------
     (K ∘T' T) aK' M ≡ K aK' (T aT M)
∘T'-app id T M = refl
∘T'-app (T' T∘ K) T M = cong (T' aT_) (∘T'-app K T M)

T∘'-app : {Γ : Ctx}
     {X Y Z : Type} →
     (T : Γ ⊢T⦂ Y ⊸ Z) →
     (K : Γ ⊢K⦂ X ⊸ Y) →
     (M : Γ ⊢M⦂ X) →
     ---------------------
     (T T∘' K) aK M ≡ T aT (K aK M)
T∘'-app T id M = refl
T∘'-app T (K ∘T T') M = T∘'-app T K (T' aT M)

to-app : {Γ : Ctx}
     {X Y : Type} →
     (K : Γ ⊢K⦂ X ⊸ Y) →
     (M : Γ ⊢M⦂ X) →
     ---------------------
     K aK M ≡ (to K) aK' M
to-app id M = refl
to-app (K ∘T T) M rewrite ∘T'-app (to K) T M = to-app K (T aT M)

from-app : {Γ : Ctx}
     {X Y : Type} →
     (K : Γ ⊢K'⦂ X ⊸ Y) →
     (M : Γ ⊢M⦂ X) →
     ---------------------
     K aK' M ≡ (from K) aK M
from-app id M = refl
from-app (T T∘ K) M rewrite T∘'-app T (from K) M = cong (T aT_) (from-app K M)