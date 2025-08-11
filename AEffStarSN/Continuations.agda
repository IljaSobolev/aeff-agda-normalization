open import AEffStarSN.AEffStar

module AEffStarSN.Continuations where

infixl 20 _∘_

data _⊢K⦂_⊸_ (Γ : Ctx) (X : Type) : Type → Set where

  id  : -----------
        Γ ⊢K⦂ X ⊸ X

  _∘_ : {Y Z : Type} →
        Γ ⊢K⦂ Y ⊸ Z →
        Γ ⊢T⦂ X ⊸ Y →
        -----------
        Γ ⊢K⦂ X ⊸ Z

infix 20 _aK_

_aK_ : {Γ : Ctx} {X Y : Type} →
       Γ ⊢K⦂ X ⊸ Y →
       Γ ⊢M⦂ X →
       ------
       Γ ⊢M⦂ Y
id aK M = M
(K ∘ T) aK M = K aK (T aT M)

data _`aK_`↝_ {Γ : Ctx} {X : Type} : {Y : Type} → Γ ⊢K⦂ X ⊸ Y → Γ ⊢M⦂ X → Γ ⊢M⦂ Y → Set where

  `id : {M : Γ ⊢M⦂ X} {N : Γ ⊢M⦂ X} →
        M ↝ N →
        -------------
        id `aK M `↝ N

  `aK : {Y Z : Type} {M : Γ ⊢M⦂ X} {N : Γ ⊢M⦂ Y}
        (K : Γ ⊢K⦂ Y ⊸ Z) {T : Γ ⊢T⦂ X ⊸ Y} →
        T aT M ↝ N →
        -------------------------
        (K ∘ T) `aK M `↝ (K aK N)

context-K : {Γ : Ctx} {X Y : Type} {M N : Γ ⊢M⦂ X}
            (K : Γ ⊢K⦂ X ⊸ Y) →
            M ↝ N →
            ---------------
            K aK M ↝ K aK N
context-K id r = r
context-K (K ∘ T) r = context-K K (context-T T r)

aK→`aK : {Γ : Ctx} {X Y : Type} {M : Γ ⊢M⦂ X} {N : Γ ⊢M⦂ Y}
         (K : Γ ⊢K⦂ X ⊸ Y) →
         K aK M ↝ N →
         ----------
         K `aK M `↝ N
aK→`aK id r = `id r
aK→`aK (K ∘ T) r with aK→`aK K r
... | `id _ = `aK _ r
... | `aK _ (context-T _ r) = `aK _ r