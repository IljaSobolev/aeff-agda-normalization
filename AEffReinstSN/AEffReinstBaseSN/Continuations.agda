{-# OPTIONS --guardedness #-}

open import AEffReinstSN.AEffReinstBaseSN.AEff

open import Data.Nat using (ℕ; zero; suc)

open import AEffReinstSN.CoinductiveEffectAnnotations using (Σₛ)
open import AEffReinstSN.AEff using (payload)

module AEffReinstSN.AEffReinstBaseSN.Continuations where

variable
  m n k : ℕ

infixl 20 _∘l_
infixl 20 _∘↓_,_
infixl 20 _∘c

data _⊢K⦂_⊸_[_] (Γ : Ctx) (X : Type) : Type → ℕ → Set where

  id   : -----------
         Γ ⊢K⦂ X ⊸ X [ 0 ]

  _∘l_ : Γ ⊢K⦂ Y ⊸ Z [ n ] →
         Γ ∷ X ⊢M⦂ Y →
         -----------
         Γ ⊢K⦂ X ⊸ Z [ n ]

  _∘↓_,_ : Γ ⊢K⦂ X ⊸ Z [ n ] →
           (op : Σₛ) →
           Γ ⊢V⦂ ```(payload op) →
           -----------
           Γ ⊢K⦂ X ⊸ Z [ suc n ]

  _∘c  : Γ ⊢K⦂ X ⊸ Z [ n ] →
         -----------
         Γ ⊢K⦂ X ⊸ Z [ n ]

infix 20 _aK_

_aK_ : Γ ⊢K⦂ X ⊸ Y [ n ] → Γ ⊢M⦂ X → Γ ⊢M⦂ Y
id aK M = M
(K ∘l N) aK M = K aK (let= M `in N)
(K ∘↓ op , V) aK M = K aK (↓ op V M)
(K ∘c) aK M = K aK (coerce M)

data _`aK_`↝_ : Γ ⊢K⦂ X ⊸ Y [ n ] → Γ ⊢M⦂ X → Γ ⊢M⦂ Y → Set where

  `id  : M ↝ M' →
         -------------
         id `aK M `↝ M'

  `aKl : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
         let= M `in N ↝ L →
         -------------------------
         (K ∘l N) `aK M `↝ (K aK L)

  `aK↓ : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
         ↓ op V M ↝ L →
         --------------------
         (K ∘↓ op , V) `aK M `↝ (K aK L)

  `aKc : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
         coerce M ↝ L →
         -------------------
         (K ∘c) `aK M `↝ (K aK L)

context-K : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) →
            M ↝ M' →
            ---------------
            K aK M ↝ K aK M'
context-K id r = r
context-K (K ∘l _) r = context-K K (context-T _ r)
context-K (K ∘↓ _ , _) r = context-K K (context-T _ r)
context-K (K ∘c) r = context-K K (context-T _ r)

aK→`aK : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) →
         K aK M ↝ N →
         ----------
         K `aK M `↝ N
aK→`aK id r = `id r
aK→`aK (K ∘l _) r with aK→`aK K r
... | `id _ = `aKl _ r
... | `aKl _ (context-T _ r) = `aKl _ r
... | `aK↓ _ (context-T _ r) = `aKl _ r
... | `aKc _ (context-T _ r) = `aKl _ r
aK→`aK (K ∘↓ _ , _) r with aK→`aK K r
... | `id _ = `aK↓ _ r
... | `aKl _ (context-T _ r) = `aK↓ _ r
... | `aK↓ _ (context-T _ r) = `aK↓ _ r
... | `aKc _ (context-T _ r) = `aK↓ _ r
aK→`aK (K ∘c) r with aK→`aK K r
... | `id _ = `aKc _ r
... | `aKl _ (context-T _ r) = `aKc _ r
... | `aK↓ _ (context-T _ r) = `aKc _ r
... | `aKc _ (context-T _ r) = `aKc _ r