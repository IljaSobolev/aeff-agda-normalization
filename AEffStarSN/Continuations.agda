open import AEffStarSN.AEffStar

module AEffStarSN.Continuations where

infixl 20 _∘_

data _⊢K⦂_⊸_ (Γ : Ctx) (X : Type) : Type → Set where

  id  : -----------
        Γ ⊢K⦂ X ⊸ X

  _∘_ : Γ ⊢K⦂ Y ⊸ Z →
        Γ ⊢T⦂ X ⊸ Y →
        -----------
        Γ ⊢K⦂ X ⊸ Z

infix 20 _aK_

_aK_ : Γ ⊢K⦂ X ⊸ Y →
       Γ ⊢M⦂ X →
       ------
       Γ ⊢M⦂ Y
id aK M = M
(K ∘ T) aK M = K aK (T aT M)

data _`aK_`↝_ : Γ ⊢K⦂ X ⊸ Y → Γ ⊢M⦂ X → Γ ⊢M⦂ Y → Set where

  `id : M ↝ M' →
        -------------
        id `aK M `↝ M'

  `aK : (K : Γ ⊢K⦂ Y ⊸ Z)→
        T aT M ↝ N →
        -------------------------
        (K ∘ T) `aK M `↝ (K aK N)

context-K : (K : Γ ⊢K⦂ X ⊸ Y) →
            M ↝ M' →
            ---------------
            K aK M ↝ K aK M'
context-K id r = r
context-K (K ∘ T) r = context-K K (context-T T r)

aK→`aK : (K : Γ ⊢K⦂ X ⊸ Y) →
         K aK M ↝ N →
         ----------
         K `aK M `↝ N
aK→`aK id r = `id r
aK→`aK (K ∘ T) r with aK→`aK K r
... | `id _ = `aK _ r
... | `aK _ (context-T _ r) = `aK _ r