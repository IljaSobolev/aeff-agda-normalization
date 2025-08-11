-- the code in this file is adapted from Programming Language Foundations in Agda, available under the CC BY 4.0 license
-- https://plfa.inf.ed.ac.uk/20.07/Substitution/
-- https://creativecommons.org/licenses/by/4.0/deed.en

open import AEffStarSN.AEffStar

open import Data.List using ([]) renaming (_∷_ to _∷ₗ_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_)

open import Types using (BType)

module AEffStarSN.SubstitutionProperties where

data _⊢_ (Γ : Ctx) (X : Type) : Set where
  ⊢V : Γ ⊢V⦂ X → Γ ⊢ X
  ⊢M : Γ ⊢M⦂ X → Γ ⊢ X
  ⊢T : {Y : Type} → Γ ⊢T⦂ Y ⊸ X → Γ ⊢ X

rename : {X : Type} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢ X → Γ' ⊢ X
rename r (⊢V V) = ⊢V (V-rename r V)
rename r (⊢M M) = ⊢M (M-rename r M)
rename r (⊢T T) = ⊢T (T-rename r T)

infix 40 _[_]

_[_] : {Γ Γ' : Ctx} {X : Type} → Γ ⊢ X → Sub Γ Γ' → Γ' ⊢ X
⊢V V [ s ] = ⊢V (V [ s ]v)
⊢M M [ s ] = ⊢M (M [ s ]m)
⊢T T [ s ] = ⊢T (T [ s ]t)

⌊_⌋v : {Γ : Ctx} {X : Type} {V V' : Γ ⊢V⦂ X} → ⊢V V ≡ ⊢V V' → V ≡ V'
⌊ refl ⌋v = refl

⌈_⌉v : {Γ : Ctx} {X : Type} {V V' : Γ ⊢V⦂ X} → V ≡ V' → ⊢V V ≡ ⊢V V'
⌈ refl ⌉v = refl

⌊_⌋m : {Γ : Ctx} {X : Type} {M M' : Γ ⊢M⦂ X} → ⊢M M ≡ ⊢M M' → M ≡ M'
⌊ refl ⌋m = refl

⌈_⌉m : {Γ : Ctx} {X : Type} {M M' : Γ ⊢M⦂ X} → M ≡ M' → ⊢M M ≡ ⊢M M'
⌈ refl ⌉m = refl

⌊_⌋t : {Γ : Ctx} {X Y : Type} {T T' : Γ ⊢T⦂ Y ⊸ X} → ⊢T T ≡ ⊢T T' → T ≡ T'
⌊ refl ⌋t = refl

⌈_⌉t : {Γ : Ctx} {X Y : Type} {T T' : Γ ⊢T⦂ Y ⊸ X} → T ≡ T' → ⊢T T ≡ ⊢T T'
⌈ refl ⌉t = refl

cong-ren : {Γ Γ' : Ctx} {X : Type} {T : Γ ⊢ X}
           {r r' : Ren Γ Γ'} →
           ({Y : Type} (x : Y ∈ Γ) → r x ≡ r' x) →
           ------------------------
           rename r T ≡ rename r' T

cong-ren-l : {Γ Γ' : Ctx} {X Y : Type} {T : Γ ∷ X ⊢ Y}
             {r r' : Ren Γ Γ'} →
             ({Y : Type} (x : Y ∈ Γ) → r x ≡ r' x) →
             ------------------------------------
             rename (wk₂ r) T ≡ rename (wk₂ r') T
cong-ren-l f = cong-ren (λ {Hd → refl; (Tl x) → cong Tl (f x)})

cong-ren {T = ⊢V (` x)} f = ⌈ cong `_ (f x) ⌉v
cong-ren {T = ⊢V (`` c)} f = refl
cong-ren {T = ⊢V (ƛ M)} f = ⌈ cong ƛ ⌊ cong-ren-l f ⌋m ⌉v
cong-ren {T = ⊢V ⟨ V ⟩} f = ⌈ cong ⟨_⟩ ⌊ cong-ren f ⌋v ⌉v
cong-ren {T = ⊢V ★} f = refl

cong-ren {T = ⊢M (return V)} f = ⌈ cong return ⌊ cong-ren f ⌋v ⌉m
cong-ren {T = ⊢M (V · W)} f = ⌈ cong₂ _·_ ⌊ cong-ren f ⌋v ⌊ cong-ren f ⌋v ⌉m
cong-ren {T = ⊢M (↑ op V M)} f = ⌈ cong₂ (↑ op) ⌊ cong-ren f ⌋v ⌊ cong-ren f ⌋m ⌉m
cong-ren {T = ⊢M (promise op ↦ M `in N)} f = ⌈ cong₂ (promise op ↦_`in_) ⌊ cong-ren-l f ⌋m ⌊ cong-ren-l f ⌋m ⌉m
cong-ren {T = ⊢M (await V until M)} f = ⌈ cong₂ await_until_ ⌊ cong-ren f ⌋v ⌊ cong-ren-l f ⌋m ⌉m
cong-ren {T = ⊢M (T aT M)} f = ⌈ cong₂ _aT_ ⌊ cong-ren f ⌋t ⌊ cong-ren f ⌋m ⌉m

cong-ren {T = ⊢T (Tl N)} f = ⌈ cong Tl ⌊ cong-ren-l f ⌋m ⌉t
cong-ren {T = ⊢T (T↓ op V)} f = ⌈ cong (T↓ op) ⌊ cong-ren f ⌋v ⌉t
cong-ren {T = ⊢T Tc} f = refl

cong-sub : {Γ Γ' : Ctx} {X : Type} {T : Γ ⊢ X}
           {s s' : Sub Γ Γ'} →
           ({Y : Type} (x : Y ∈ Γ) → s x ≡ s' x) →
           ------------------
           T [ s ] ≡ T [ s' ]

cong-sub-l : {Γ Γ' : Ctx} {X Y : Type} {T : Γ ∷ X ⊢ Y}
             {s s' : Sub Γ Γ'} →
             ({Y : Type} (x : Y ∈ Γ) → s x ≡ s' x) →
             ----------------------------
             T [ lift s ] ≡ T [ lift s' ]
cong-sub-l f = cong-sub (λ {Hd → refl; (Tl x) → cong (V-rename Tl) (f x)})

cong-sub {T = ⊢V (` x)} f = ⌈ f x ⌉v
cong-sub {T = ⊢V (`` c)} f = refl
cong-sub {T = ⊢V (ƛ M)} f = ⌈ cong ƛ ⌊ cong-sub-l f ⌋m ⌉v
cong-sub {T = ⊢V ⟨ V ⟩} f = ⌈ cong ⟨_⟩ ⌊ cong-sub {T = ⊢V V} f ⌋v ⌉v
cong-sub {T = ⊢V ★} f = refl

cong-sub {T = ⊢M (return V)} f = ⌈ cong return ⌊ cong-sub {T = ⊢V V} f ⌋v ⌉m
cong-sub {T = ⊢M (V · W)} f = ⌈ cong₂ _·_ ⌊ cong-sub {T = ⊢V V} f ⌋v ⌊ cong-sub {T = ⊢V W} f ⌋v ⌉m
cong-sub {T = ⊢M (↑ op V M)} f = ⌈ cong₂ (↑ op) ⌊ cong-sub {T = ⊢V V} f ⌋v ⌊ cong-sub f ⌋m ⌉m
cong-sub {T = ⊢M (promise op ↦ M `in N)} f = ⌈ cong₂ (promise op ↦_`in_) ⌊ cong-sub-l f ⌋m ⌊ cong-sub-l f ⌋m ⌉m
cong-sub {T = ⊢M (await V until M)} f = ⌈ cong₂ await_until_ ⌊ cong-sub {T = ⊢V V} f ⌋v ⌊ cong-sub-l f ⌋m ⌉m
cong-sub {T = ⊢M (T aT M)} f = ⌈ cong₂ _aT_ ⌊ cong-sub f ⌋t ⌊ cong-sub f ⌋m ⌉m

cong-sub {T = ⊢T (Tl N)} f = ⌈ cong Tl ⌊ cong-sub-l f ⌋m ⌉t
cong-sub {T = ⊢T (T↓ op V)} f = ⌈ cong (T↓ op) ⌊ cong-sub {T = ⊢V V} f ⌋v ⌉t
cong-sub {T = ⊢T Tc} f = refl

ren-id : {Γ : Ctx} {X : Type} {T : Γ ⊢ X} →
         ----------------
         rename idr T ≡ T

ren-id-l : {Γ : Ctx} {X Y : Type} {T : Γ ∷ X ⊢ Y} →
           -----------------------
           rename (wk₂ idr) T ≡ T
ren-id-l = trans (cong-ren (λ {Hd → refl; (Tl x) → refl})) ren-id

ren-id {T = ⊢V (` x)} = refl
ren-id {T = ⊢V (`` c)} = refl
ren-id {T = ⊢V (ƛ M)} = ⌈ cong ƛ ⌊ ren-id-l ⌋m ⌉v
ren-id {T = ⊢V ⟨ V ⟩} = ⌈ cong ⟨_⟩ ⌊ ren-id ⌋v ⌉v
ren-id {T = ⊢V ★} = refl

ren-id {T = ⊢M (return V)} = ⌈ cong return ⌊ ren-id ⌋v ⌉m
ren-id {T = ⊢M (V · W)} = ⌈ cong₂ _·_ ⌊ ren-id ⌋v ⌊ ren-id ⌋v ⌉m
ren-id {T = ⊢M (↑ op V M)} = ⌈ cong₂ (↑ op) ⌊ ren-id ⌋v ⌊ ren-id ⌋m ⌉m
ren-id {T = ⊢M (promise op ↦ M `in N)} = ⌈ cong₂ (promise op ↦_`in_) ⌊ ren-id-l ⌋m ⌊ ren-id-l ⌋m ⌉m
ren-id {T = ⊢M (await V until M)} = ⌈ cong₂ await_until_ ⌊ ren-id ⌋v ⌊ ren-id-l ⌋m ⌉m
ren-id {T = ⊢M (T aT M)} = ⌈ cong₂ _aT_ ⌊ ren-id ⌋t ⌊ ren-id ⌋m ⌉m

ren-id {T = ⊢T (Tl N)} = ⌈ cong Tl ⌊ ren-id-l ⌋m ⌉t
ren-id {T = ⊢T (T↓ op V)} = ⌈ cong (T↓ op) ⌊ ren-id ⌋v ⌉t
ren-id {T = ⊢T Tc} = refl

sub-id : {Γ : Ctx} {X : Type} {T : Γ ⊢ X} →
         -------------
         T [ ids ] ≡ T

sub-id-l : {Γ : Ctx} {X Y : Type} {T : Γ ∷ X ⊢ Y} →
           ------------------
           T [ lift ids ] ≡ T
sub-id-l = trans (cong-sub (λ {Hd → refl; (Tl x) → refl})) sub-id

sub-id {T = ⊢V (` x)} = refl
sub-id {T = ⊢V (`` c)} = refl
sub-id {T = ⊢V (ƛ M)} = ⌈ cong ƛ ⌊ sub-id-l ⌋m ⌉v
sub-id {T = ⊢V ⟨ V ⟩} = ⌈ cong ⟨_⟩ ⌊ sub-id ⌋v ⌉v
sub-id {T = ⊢V ★} = refl

sub-id {T = ⊢M (return V)} = ⌈ cong return ⌊ sub-id ⌋v ⌉m
sub-id {T = ⊢M (V · W)} = ⌈ cong₂ _·_ ⌊ sub-id ⌋v ⌊ sub-id ⌋v ⌉m
sub-id {T = ⊢M (↑ op V M)} = ⌈ cong₂ (↑ op) ⌊ sub-id ⌋v ⌊ sub-id ⌋m ⌉m
sub-id {T = ⊢M (promise op ↦ M `in N)} = ⌈ cong₂ (promise op ↦_`in_) ⌊ sub-id-l ⌋m ⌊ sub-id-l ⌋m ⌉m
sub-id {T = ⊢M (await V until M)} = ⌈ cong₂ await_until_ ⌊ sub-id ⌋v ⌊ sub-id-l ⌋m ⌉m
sub-id {T = ⊢M (T aT M)} = ⌈ cong₂ _aT_ ⌊ sub-id ⌋t ⌊ sub-id ⌋m ⌉m

sub-id {T = ⊢T (Tl N)} = ⌈ cong Tl ⌊ sub-id-l ⌋m ⌉t
sub-id {T = ⊢T (T↓ op V)} = ⌈ cong (T↓ op) ⌊ sub-id ⌋v ⌉t
sub-id {T = ⊢T Tc} = refl

ren-ren : {Γ Γ' Γ'' : Ctx} {X : Type} {T : Γ ⊢ X}
          {r : Ren Γ' Γ''} {r' : Ren Γ Γ'} →
          ------------------------------------------
          rename r (rename r' T) ≡ rename (r ∘ r') T

ren-ren-l : {Γ Γ' Γ'' : Ctx} {X Y : Type} {T : Γ ∷ X ⊢ Y}
            {r : Ren Γ' Γ''} {r' : Ren Γ Γ'} →
            ------------------------------------------------------------
            rename (wk₂ r) (rename (wk₂ r') T) ≡ rename (wk₂ (r ∘ r')) T
ren-ren-l = trans ren-ren (cong-ren (λ {Hd → refl; (Tl x) → refl}))

ren-ren {T = ⊢V (` x)} = refl
ren-ren {T = ⊢V (`` c)} = refl
ren-ren {T = ⊢V (ƛ M)} = ⌈ cong ƛ ⌊ ren-ren-l ⌋m ⌉v
ren-ren {T = ⊢V ⟨ V ⟩} = ⌈ cong ⟨_⟩ ⌊ ren-ren ⌋v ⌉v
ren-ren {T = ⊢V ★} = refl

ren-ren {T = ⊢M (return V)} = ⌈ cong return ⌊ ren-ren ⌋v ⌉m
ren-ren {T = ⊢M (V · W)} = ⌈ cong₂ _·_ ⌊ ren-ren ⌋v ⌊ ren-ren ⌋v ⌉m
ren-ren {T = ⊢M (↑ op V M)} = ⌈ cong₂ (↑ op) ⌊ ren-ren ⌋v ⌊ ren-ren ⌋m ⌉m
ren-ren {T = ⊢M (promise op ↦ M `in N)} = ⌈ cong₂ (promise op ↦_`in_) ⌊ ren-ren-l ⌋m ⌊ ren-ren-l ⌋m ⌉m
ren-ren {T = ⊢M (await V until M)} = ⌈ cong₂ await_until_ ⌊ ren-ren ⌋v ⌊ ren-ren-l ⌋m ⌉m
ren-ren {T = ⊢M (T aT M)} = ⌈ cong₂ _aT_ ⌊ ren-ren ⌋t ⌊ ren-ren ⌋m ⌉m

ren-ren {T = ⊢T (Tl N)} = ⌈ cong Tl ⌊ ren-ren-l ⌋m ⌉t
ren-ren {T = ⊢T (T↓ op V)} = ⌈ cong (T↓ op) ⌊ ren-ren ⌋v ⌉t
ren-ren {T = ⊢T Tc} = refl

sub-ren : {Γ Γ' Δ Δ' : Ctx} {X : Type} {T : Γ ⊢ X}
          {s : Sub Γ Δ} {s' : Sub Γ' Δ'}
          {rΓ : Ren Γ Γ'} {rΔ : Ren Δ Δ'} →
          ({Y : Type} (x : Y ∈ Γ) → s' (rΓ x) ≡ V-rename rΔ (s x)) →
          ------------------------------------------
          rename rΓ T [ s' ] ≡ rename rΔ (T [ s ])

sub-ren-var : {Γ Γ' Δ Δ' : Ctx} {X : Type}
              {s : Sub Γ Δ } {s' : Sub Γ' Δ'}
              {rΓ : Ren Γ Γ'} {rΔ : Ren Δ Δ'} →
              ({Y : Type} (x : Y ∈ Γ) → s' (rΓ x) ≡ V-rename rΔ (s x)) →
              --------------------------------------------------
              ({Y : Type} (x : Y ∈ Γ) → V-rename (Tl {Y = X}) (s' (rΓ x)) ≡ V-rename (wk₂ rΔ) (V-rename Tl (s x)))
sub-ren-var {s = s} {s'} {rΓ} {rΔ} H x =
  begin
    V-rename Tl (s' (rΓ x))
  ≡⟨ cong (V-rename Tl) (H x) ⟩
    V-rename Tl (V-rename rΔ (s x))
  ≡⟨ ⌊ ren-ren ⌋v ⟩
    V-rename (Tl ∘ rΔ) (s x)
  ≡⟨ sym ⌊ ren-ren ⌋v ⟩
    V-rename (wk₂ rΔ) (V-rename Tl (s x))
  ∎

sub-ren-l : {Γ Γ' Δ Δ' : Ctx} {X Y : Type} {T : Γ ∷ X ⊢ Y}
            {s : Sub Γ Δ } {s' : Sub Γ' Δ'}
            {rΓ : Ren Γ Γ'} {rΔ : Ren Δ Δ'} →
            ({Y : Type} (x : Y ∈ Γ) → s' (rΓ x) ≡ V-rename rΔ (s x)) →
            --------------------------------------------------------------
            rename (wk₂ rΓ) T [ lift s' ] ≡ rename (wk₂ rΔ) (T [ lift s ])
sub-ren-l {s' = s'} {rΓ} H = sub-ren (λ {Hd → refl; (Tl x) → sub-ren-var {s' = s'} {rΓ} H x})

sub-ren {T = ⊢V (` x)} f = ⌈ f x ⌉v
sub-ren {T = ⊢V (`` c)} f = refl
sub-ren {T = ⊢V (ƛ M)} f = ⌈ cong ƛ ⌊ sub-ren-l f ⌋m ⌉v
sub-ren {T = ⊢V ⟨ V ⟩} f = ⌈ cong ⟨_⟩ ⌊ sub-ren {T = ⊢V V} f ⌋v ⌉v
sub-ren {T = ⊢V ★} f = refl

sub-ren {T = ⊢M (return V)} f = ⌈ cong return ⌊ sub-ren {T = ⊢V V} f ⌋v ⌉m
sub-ren {T = ⊢M (V · W)} f = ⌈ cong₂ _·_ ⌊ sub-ren {T = ⊢V V} f ⌋v ⌊ sub-ren {T = ⊢V W} f ⌋v ⌉m
sub-ren {T = ⊢M (↑ op V M)} f = ⌈ cong₂ (↑ op) ⌊ sub-ren {T = ⊢V V} f ⌋v ⌊ sub-ren f ⌋m ⌉m
sub-ren {T = ⊢M (promise op ↦ M `in N)} f = ⌈ cong₂ (promise op ↦_`in_) ⌊ sub-ren-l f ⌋m ⌊ sub-ren-l f ⌋m ⌉m
sub-ren {T = ⊢M (await V until M)} f = ⌈ cong₂ await_until_ ⌊ sub-ren {T = ⊢V V} f ⌋v ⌊ sub-ren-l f ⌋m ⌉m
sub-ren {T = ⊢M (T aT M)} f = ⌈ cong₂ _aT_ ⌊ sub-ren f ⌋t ⌊ sub-ren f ⌋m ⌉m

sub-ren {T = ⊢T (Tl N)} f = ⌈ cong Tl ⌊ sub-ren-l f ⌋m ⌉t
sub-ren {T = ⊢T (T↓ op V)} f = ⌈ cong (T↓ op) ⌊ sub-ren {T = ⊢V V} f ⌋v ⌉t
sub-ren {T = ⊢T Tc} f = refl

sub-sub : {Γ Γ' Γ'' : Ctx} {X : Type} {T : Γ ⊢ X}
          {s : Sub Γ Γ'} {s' : Sub Γ' Γ''} →
          -----------------------------------
          T [ s ] [ s' ] ≡ T [ _[ s' ]v ∘ s ]

sub-sub-l : {Γ Γ' Γ'' : Ctx} {X Y : Type} {T : Γ ∷ X ⊢ Y} 
            {s : Sub Γ Γ'} {s' : Sub Γ' Γ''} →
            ----------------------------------------------------
            T [ lift s ] [ lift s' ] ≡ T [ lift (_[ s' ]v ∘ s) ]
sub-sub-l {s = s} = trans sub-sub (cong-sub (λ {Hd → refl; (Tl x) → ⌊ sub-ren {T = ⊢V (s x)} (λ _ → refl) ⌋v}))

sub-sub {T = ⊢V (` x)} = refl
sub-sub {T = ⊢V (`` c)} = refl
sub-sub {T = ⊢V (ƛ M)} = ⌈ cong ƛ ⌊ sub-sub-l ⌋m ⌉v
sub-sub {T = ⊢V ⟨ V ⟩} = ⌈ cong ⟨_⟩ ⌊ sub-sub {T = ⊢V V} ⌋v ⌉v
sub-sub {T = ⊢V ★} = refl

sub-sub {T = ⊢M (return V)} = ⌈ cong return ⌊ sub-sub {T = ⊢V V} ⌋v ⌉m
sub-sub {T = ⊢M (V · W)} = ⌈ cong₂ _·_ ⌊ sub-sub {T = ⊢V V} ⌋v ⌊ sub-sub {T = ⊢V W} ⌋v ⌉m
sub-sub {T = ⊢M (↑ op V M)} = ⌈ cong₂ (↑ op) ⌊ sub-sub {T = ⊢V V} ⌋v ⌊ sub-sub ⌋m ⌉m
sub-sub {T = ⊢M (promise op ↦ M `in N)} = ⌈ cong₂ (promise op ↦_`in_) ⌊ sub-sub-l ⌋m ⌊ sub-sub-l ⌋m ⌉m
sub-sub {T = ⊢M (await V until M)} = ⌈ cong₂ await_until_ ⌊ sub-sub {T = ⊢V V} ⌋v ⌊ sub-sub-l ⌋m ⌉m
sub-sub {T = ⊢M (T aT M)} = ⌈ cong₂ _aT_ ⌊ sub-sub ⌋t ⌊ sub-sub ⌋m ⌉m

sub-sub {T = ⊢T (Tl N)} = ⌈ cong Tl ⌊ sub-sub-l ⌋m ⌉t
sub-sub {T = ⊢T (T↓ op V)} = ⌈ cong (T↓ op) ⌊ sub-sub {T = ⊢V V} ⌋v ⌉t
sub-sub {T = ⊢T Tc} = refl

eq₁ : {Γ : Ctx} {X Y : Type}
      (T : Γ ⊢ X) (V : Γ ⊢V⦂ Y) →
      ---------------------------
      rename wk₁ T [ ids [ V ]s ]
      ≡
      T
eq₁ T W =
  begin
    rename wk₁ T [ ids [ W ]s ]
  ≡⟨ sub-ren {T = T} (λ {Hd → refl; (Tl x) → refl}) ⟩
    rename idr (T [ ids ])
  ≡⟨ ren-id ⟩
    T [ ids ]
  ≡⟨ sub-id ⟩
    T
  ∎

eq₂ : {Γ Γ' : Ctx} {X Y : Type}
      {s : Sub Γ Γ'}
      (T : Γ ∷ X ⊢ Y) (V : Γ' ⊢V⦂ X) →
      ---------------------------
      T [ lift s ] [ ids [ V ]s ]
      ≡
      T [ s [ V ]s ]
eq₂ {s = s} T V =
  begin
    T [ lift s ] [ ids [ V ]s ]
  ≡⟨ sub-sub ⟩
    T [ _[ ids [ V ]s ]v ∘ lift s ]
  ≡⟨ cong-sub (λ {Hd → refl; (Tl x) → ⌊ eq₁ _ V ⌋v}) ⟩
    T [ s [ V ]s ]
  ∎

eq₃ : {Γ Γ' : Ctx} {X Y : Type}
      (s : Sub Γ Γ')
      (T : Γ ∷ X ⊢ Y) (V : Γ ⊢V⦂ X) →
      ----------------------
      T [ ids [ V ]s ] [ s ]
      ≡
      T [ lift s ] [ ids [ V [ s ]v ]s ]
eq₃ s T V =
  begin
    T [ ids [ V ]s ] [ s ]
  ≡⟨ sub-sub ⟩
    T [ _[ s ]v ∘ (ids [ V ]s) ]
  ≡⟨ cong-sub (λ {Hd → refl; (Tl x) → refl}) ⟩
    T [ s [ V [ s ]v ]s ]
  ≡⟨ sym (eq₂ T (V [ s ]v)) ⟩
    T [ lift s ] [ ids [ V [ s ]v ]s ]
  ∎

eq₄ : {Γ Γ' : Ctx} {X : Type} (Z : Type)
      (s : Sub Γ Γ')
      (T : Γ ⊢ X) →
      ---------------------------------
      rename (wk₁ {X = Z}) T [ lift s ]
      ≡
      rename wk₁ (T [ s ])
eq₄ _ _ _ = sub-ren (λ {Hd → refl; (Tl x) → refl})

eq₅ : {Γ Γ' : Ctx} {X : Type} {c : BType}
      (s : Sub Γ Γ')
      (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` c) →
      --------------------------
      strengthen-val X V [ s ]v
      ≡
      strengthen-val X (V [ lift s ]v)
eq₅ s (` Tl x) with s x
... | ` y = refl
... | `` c = refl
eq₅ s (`` c) = refl

sub-↝ : {Γ Γ' : Ctx} {X : Type} {M N : Γ ⊢M⦂ X}
        (s : Sub Γ Γ') →
        M ↝ N →
        -------------------
        M [ s ]m ↝ N [ s ]m
sub-↝ s (apply M V) rewrite ⌊ eq₃ s (⊢M M) V ⌋m = apply _ _
sub-↝ s (let-return V N) rewrite ⌊ eq₃ s (⊢M N) V ⌋m = let-return _ _
sub-↝ s (T-↑ V T M) = T-↑ _ _ _
sub-↝ s (T-promise {X} T M N)  rewrite ⌊ eq₄ ⟨ X ⟩ s (⊢T T) ⌋t = T-promise _ _ _
sub-↝ s (T-await {X} T V M) rewrite ⌊ eq₄ X s (⊢T T) ⌋t = T-await _ _ _
sub-↝ s (promise-↑ V M N) rewrite eq₅ s V = promise-↑ _ _ _
sub-↝ s (↓-return V W) = ↓-return _ _
sub-↝ s (↓-promise-op {X} V M N) rewrite ⌊ eq₃ s (⊢M M) V ⌋m | ⌊ eq₄ ⟨ X ⟩ s (⊢T (T↓ _ V)) ⌋t = ↓-promise-op _ _ _
sub-↝ s (await-promise V M) rewrite ⌊ eq₃ s (⊢M M) V ⌋m = await-promise _ _
sub-↝ s (↑-discard V) = ↑-discard _
sub-↝ s (context-↑ r) = context-↑ (sub-↝ s r)
sub-↝ s (context-promise r) = context-promise (sub-↝ (lift s) r)
sub-↝ s (context-T T r) = context-T _ (sub-↝ s r)
sub-↝ s (coerce-return V) = coerce-return _