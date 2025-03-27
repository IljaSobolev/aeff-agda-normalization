open import AEff
open import Types
open import Finality
open import Substitutions
open import Renamings

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; subst)
open import Data.Product

-- term abstractions

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

-- continuations, the reflexive-transitive closure of term abstractions

data _⊢K⦂_⊸_ (Γ : Ctx) : Type → Type → Set where

  id      : {X : Type} →
            ------------
            Γ ⊢K⦂ X ⊸ X

  _∘T_    : {X Y Z : Type} →
            Γ ⊢K⦂ Y ⊸ Z →
            Γ ⊢T⦂ X ⊸ Y →
            ------------
            Γ ⊢K⦂ X ⊸ Z

-- alternative definition of continuations, similar to evaluation contexts
-- this is used only to prove the lemma K'-↝

data _⊢K'⦂_⊸_ (Γ : Ctx) : Type → Type → Set where

  id      : {X : Type} →
            ------------
            Γ ⊢K'⦂ X ⊸ X

  _T∘_    : {X Y Z : Type} →
            Γ ⊢T⦂ Y ⊸ Z →
            Γ ⊢K'⦂ X ⊸ Y →
            ------------
            Γ ⊢K'⦂ X ⊸ Z

-- application of term abstractions and continuations to terms

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

-- the two definitions K and K' are equivalent (in the sense that their applications match)

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

-- a very useful lemma about how application interacts with reduction

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

-- the same lemma about K, using the equivalence of K and K'

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

-- using K-↝ requires lots of with clauses, which do not work well with induction, so
-- we create another level of indirection

data _`aK_`↝↝_ : {Γ : Ctx} {X Y : Type} (K : Γ ⊢K⦂ X ⊸ Y) (M : Γ ⊢M⦂ X) (N : Γ ⊢M⦂ Y) → Set where

  `id : {Γ : Ctx}
        {X : Type}
        {M : Γ ⊢M⦂ X}
        {N : Γ ⊢M⦂ X} →
        M ↝↝ N →
        --------------
        id `aK M `↝↝ N

  `aK : {Γ : Ctx}
        {X Y Z : Type}
        {K : Γ ⊢K⦂ Y ⊸ Z}
        {T : Γ ⊢T⦂ X ⊸ Y}
        {M : Γ ⊢M⦂ X}
        {N : Γ ⊢M⦂ Y} →
        (T aT M) ↝↝ N →
        ---------------------------
        (K ∘T T) `aK M `↝↝ (K aK N)

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

`aK→aK : {Γ : Ctx}
         {X Y : Type}
         {K : Γ ⊢K⦂ X ⊸ Y}
         {M : Γ ⊢M⦂ X}
         {N : Γ ⊢M⦂ Y} →
         K `aK M `↝↝ N →
         ----------------
         K aK M ↝↝ N
`aK→aK (`id r) = r
`aK→aK (`aK {K = K} r) = aK-↝↝ K r

aK→`aK : {Γ : Ctx}
         {X Y : Type}
         {K : Γ ⊢K⦂ X ⊸ Y}
         {M : Γ ⊢M⦂ X}
         {N : Γ ⊢M⦂ Y} →
         K aK M ↝↝ N →
         ----------------
         K `aK M `↝↝ N
aK→`aK {K = id} r = `id r
aK→`aK {K = K ∘T T} r with K-↝ K _ T r
... | _ , refl , r' = `aK r'