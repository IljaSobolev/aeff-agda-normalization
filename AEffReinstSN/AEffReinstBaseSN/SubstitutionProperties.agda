-- the code in this file is adapted from Programming Language Foundations in Agda, available under the CC BY 4.0 license
-- https://plfa.inf.ed.ac.uk/20.07/Substitution/
-- https://creativecommons.org/licenses/by/4.0/deed.en

{-# OPTIONS --guardedness #-}

open import AEffReinstSN.AEffReinstBaseSN.AEff

open import Data.List using ([]) renaming (_∷_ to _∷ₗ_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_)

module AEffReinstSN.AEffReinstBaseSN.SubstitutionProperties where

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
cong₃ f refl refl refl = refl

data _⊢_ (Γ : Ctx) (Y : Type) : Set where
  ⊢V : Γ ⊢V⦂ Y → Γ ⊢ Y
  ⊢M : Γ ⊢M⦂ Y → Γ ⊢ Y
  ⊢T : Γ ⊢T⦂ X ⊸ Y → Γ ⊢ Y

rename : Ren Γ Γ' → Γ ⊢ X → Γ' ⊢ X
rename r (⊢V V) = ⊢V (V-rename r V)
rename r (⊢M M) = ⊢M (M-rename r M)
rename r (⊢T T) = ⊢T (T-rename r T)

infix 40 _[_]

_[_] : Γ ⊢ X → Sub Γ Γ' → Γ' ⊢ X
⊢V V [ s ] = ⊢V (V [ s ]v)
⊢M M [ s ] = ⊢M (M [ s ]m)
⊢T T [ s ] = ⊢T (T [ s ]t)

⌊_⌋v : ⊢V V ≡ ⊢V V' → V ≡ V'
⌊ refl ⌋v = refl

⌈_⌉v : V ≡ V' → ⊢V V ≡ ⊢V V'
⌈ refl ⌉v = refl

⌊_⌋m : ⊢M M ≡ ⊢M M' → M ≡ M'
⌊ refl ⌋m = refl

⌈_⌉m :  M ≡ M' → ⊢M M ≡ ⊢M M'
⌈ refl ⌉m = refl

⌊_⌋t : ⊢T T ≡ ⊢T T' → T ≡ T'
⌊ refl ⌋t = refl

⌈_⌉t : T ≡ T' → ⊢T T ≡ ⊢T T'
⌈ refl ⌉t = refl

variable
  TT : Γ ⊢ X

cong-ren : ({Y : Type} (x : Y ∈ Γ) → r x ≡ r' x) →
           ------------------------
           rename r TT ≡ rename r' TT

cong-ren-var : ({Y : Type} (x : Y ∈ Γ) → r x ≡ r' x) →
               -------------------
               ({Y Z : Type} (x : Y ∈ Γ ∷ Z) → wk₂ r x ≡ wk₂ r' x)
cong-ren-var f Hd = refl
cong-ren-var f (Tl x) = cong Tl (f x)

cong-ren-l : ({Y : Type} (x : Y ∈ Γ) → r x ≡ r' x) →
             ------------------------------------
             rename (wk₂ r) TT ≡ rename (wk₂ r') TT
cong-ren-l f = cong-ren (cong-ren-var f)

cong-ren {TT = ⊢V (` x)} f = ⌈ cong `_ (f x) ⌉v
cong-ren {TT = ⊢V (`` c)} f = refl
cong-ren {TT = ⊢V (ƛ M)} f = ⌈ cong ƛ ⌊ cong-ren-l f ⌋m ⌉v
cong-ren {TT = ⊢V ⟨ V ⟩} f = ⌈ cong ⟨_⟩ ⌊ cong-ren f ⌋v ⌉v
cong-ren {TT = ⊢V (inl V)} f = ⌈ cong inl ⌊ cong-ren f ⌋v ⌉v
cong-ren {TT = ⊢V (inr V)} f = ⌈ cong inr ⌊ cong-ren f ⌋v ⌉v
cong-ren {TT = ⊢V ★} f = refl
cong-ren {TT = ⊢V u} f = refl

cong-ren {TT = ⊢M (return V)} f = ⌈ cong return ⌊ cong-ren f ⌋v ⌉m
cong-ren {TT = ⊢M (V · W)} f = ⌈ cong₂ _·_ ⌊ cong-ren f ⌋v ⌊ cong-ren f ⌋v ⌉m
cong-ren {TT = ⊢M (↑ op V M)} f = ⌈ cong₂ (↑ op) ⌊ cong-ren f ⌋v ⌊ cong-ren f ⌋m ⌉m
cong-ren {TT = ⊢M (promise op ↦ M `in N)} f = ⌈ cong₂ (promise op ↦_`in_) ⌊ cong-ren-l f ⌋m ⌊ cong-ren-l f ⌋m ⌉m
cong-ren {TT = ⊢M (await V until M)} f = ⌈ cong₂ await_until_ ⌊ cong-ren f ⌋v ⌊ cong-ren-l f ⌋m ⌉m
cong-ren {TT = ⊢M (match+ V M N)} f = ⌈ cong₃ match+ ⌊ cong-ren f ⌋v ⌊ cong-ren-l f ⌋m ⌊ cong-ren-l f ⌋m ⌉m
cong-ren {TT = ⊢M (T aT M)} f = ⌈ cong₂ _aT_ ⌊ cong-ren f ⌋t ⌊ cong-ren f ⌋m ⌉m

cong-ren {TT = ⊢T (Tl N)} f = ⌈ cong Tl ⌊ cong-ren-l f ⌋m ⌉t
cong-ren {TT = ⊢T (T↓ op V)} f = ⌈ cong (T↓ op) ⌊ cong-ren f ⌋v ⌉t
cong-ren {TT = ⊢T Tc} f = refl

cong-sub : ({Y : Type} (x : Y ∈ Γ) → s x ≡ s' x) →
           ------------------
           TT [ s ] ≡ TT [ s' ]

cong-sub-var : ({Y : Type} (x : Y ∈ Γ) → s x ≡ s' x) →
               ------------------
               ({Y Z : Type} (x : Y ∈ Γ ∷ Z) → lift s x ≡ lift s' x)
cong-sub-var f Hd = refl
cong-sub-var f (Tl x) = cong (V-rename Tl) (f x)

cong-sub-l : ({Y : Type} (x : Y ∈ Γ) → s x ≡ s' x) →
             ----------------------------
             TT [ lift s ] ≡ TT [ lift s' ]
cong-sub-l f = cong-sub (cong-sub-var f)

cong-sub {TT = ⊢V (` x)} f = ⌈ f x ⌉v
cong-sub {TT = ⊢V (`` c)} f = refl
cong-sub {TT = ⊢V (ƛ M)} f = ⌈ cong ƛ ⌊ cong-sub-l f ⌋m ⌉v
cong-sub {TT = ⊢V ⟨ V ⟩} f = ⌈ cong ⟨_⟩ ⌊ cong-sub {TT = ⊢V V} f ⌋v ⌉v
cong-sub {TT = ⊢V (inl V)} f = ⌈ cong inl ⌊ cong-sub {TT = ⊢V V} f ⌋v ⌉v
cong-sub {TT = ⊢V (inr V)} f = ⌈ cong inr ⌊ cong-sub {TT = ⊢V V} f ⌋v ⌉v
cong-sub {TT = ⊢V ★} f = refl
cong-sub {TT = ⊢V u} f = refl

cong-sub {TT = ⊢M (return V)} f = ⌈ cong return ⌊ cong-sub {TT = ⊢V V} f ⌋v ⌉m
cong-sub {TT = ⊢M (V · W)} f = ⌈ cong₂ _·_ ⌊ cong-sub {TT = ⊢V V} f ⌋v ⌊ cong-sub {TT = ⊢V W} f ⌋v ⌉m
cong-sub {TT = ⊢M (↑ op V M)} f = ⌈ cong₂ (↑ op) ⌊ cong-sub {TT = ⊢V V} f ⌋v ⌊ cong-sub f ⌋m ⌉m
cong-sub {TT = ⊢M (promise op ↦ M `in N)} f = ⌈ cong₂ (promise op ↦_`in_) ⌊ cong-sub-l f ⌋m ⌊ cong-sub-l f ⌋m ⌉m
cong-sub {TT = ⊢M (await V until M)} f = ⌈ cong₂ await_until_ ⌊ cong-sub {TT = ⊢V V} f ⌋v ⌊ cong-sub-l f ⌋m ⌉m
cong-sub {TT = ⊢M (match+ V M N)} f = ⌈ cong₃ match+ ⌊ cong-sub {TT = ⊢V V} f ⌋v ⌊ cong-sub-l f ⌋m ⌊ cong-sub-l f ⌋m ⌉m
cong-sub {TT = ⊢M (T aT M)} f = ⌈ cong₂ _aT_ ⌊ cong-sub f ⌋t ⌊ cong-sub f ⌋m ⌉m

cong-sub {TT = ⊢T (Tl N)} f = ⌈ cong Tl ⌊ cong-sub-l f ⌋m ⌉t
cong-sub {TT = ⊢T (T↓ op V)} f = ⌈ cong (T↓ op) ⌊ cong-sub {TT = ⊢V V} f ⌋v ⌉t
cong-sub {TT = ⊢T Tc} f = refl

ren-id : rename idr TT ≡ TT

ren-id-l : rename (wk₂ idr) TT ≡ TT
ren-id-l = trans (cong-ren (λ {Hd → refl; (Tl x) → refl})) ren-id

ren-id {TT = ⊢V (` x)} = refl
ren-id {TT = ⊢V (`` c)} = refl
ren-id {TT = ⊢V (ƛ M)} = ⌈ cong ƛ ⌊ ren-id-l ⌋m ⌉v
ren-id {TT = ⊢V ⟨ V ⟩} = ⌈ cong ⟨_⟩ ⌊ ren-id ⌋v ⌉v
ren-id {TT = ⊢V (inl V)} = ⌈ cong inl ⌊ ren-id ⌋v ⌉v
ren-id {TT = ⊢V (inr V)} = ⌈ cong inr ⌊ ren-id ⌋v ⌉v
ren-id {TT = ⊢V ★} = refl
ren-id {TT = ⊢V u} = refl

ren-id {TT = ⊢M (return V)} = ⌈ cong return ⌊ ren-id ⌋v ⌉m
ren-id {TT = ⊢M (V · W)} = ⌈ cong₂ _·_ ⌊ ren-id ⌋v ⌊ ren-id ⌋v ⌉m
ren-id {TT = ⊢M (↑ op V M)} = ⌈ cong₂ (↑ op) ⌊ ren-id ⌋v ⌊ ren-id ⌋m ⌉m
ren-id {TT = ⊢M (promise op ↦ M `in N)} = ⌈ cong₂ (promise op ↦_`in_) ⌊ ren-id-l ⌋m ⌊ ren-id-l ⌋m ⌉m
ren-id {TT = ⊢M (await V until M)} = ⌈ cong₂ await_until_ ⌊ ren-id ⌋v ⌊ ren-id-l ⌋m ⌉m
ren-id {TT = ⊢M (match+ V M N)} = ⌈ cong₃ match+ ⌊ ren-id ⌋v ⌊ ren-id-l ⌋m ⌊ ren-id-l ⌋m ⌉m
ren-id {TT = ⊢M (T aT M)} = ⌈ cong₂ _aT_ ⌊ ren-id ⌋t ⌊ ren-id ⌋m ⌉m

ren-id {TT = ⊢T (Tl N)} = ⌈ cong Tl ⌊ ren-id-l ⌋m ⌉t
ren-id {TT = ⊢T (T↓ op V)} = ⌈ cong (T↓ op) ⌊ ren-id ⌋v ⌉t
ren-id {TT = ⊢T Tc} = refl

sub-id : TT [ ids ] ≡ TT

sub-id-l : TT [ lift ids ] ≡ TT
sub-id-l = trans (cong-sub (λ {Hd → refl; (Tl x) → refl})) sub-id

sub-id {TT = ⊢V (` x)} = refl
sub-id {TT = ⊢V (`` c)} = refl
sub-id {TT = ⊢V (ƛ M)} = ⌈ cong ƛ ⌊ sub-id-l ⌋m ⌉v
sub-id {TT = ⊢V ⟨ V ⟩} = ⌈ cong ⟨_⟩ ⌊ sub-id ⌋v ⌉v
sub-id {TT = ⊢V (inl V)} = ⌈ cong inl ⌊ sub-id ⌋v ⌉v
sub-id {TT = ⊢V (inr V)} = ⌈ cong inr ⌊ sub-id ⌋v ⌉v
sub-id {TT = ⊢V ★} = refl
sub-id {TT = ⊢V u} = refl

sub-id {TT = ⊢M (return V)} = ⌈ cong return ⌊ sub-id ⌋v ⌉m
sub-id {TT = ⊢M (V · W)} = ⌈ cong₂ _·_ ⌊ sub-id ⌋v ⌊ sub-id ⌋v ⌉m
sub-id {TT = ⊢M (↑ op V M)} = ⌈ cong₂ (↑ op) ⌊ sub-id ⌋v ⌊ sub-id ⌋m ⌉m
sub-id {TT = ⊢M (promise op ↦ M `in N)} = ⌈ cong₂ (promise op ↦_`in_) ⌊ sub-id-l ⌋m ⌊ sub-id-l ⌋m ⌉m
sub-id {TT = ⊢M (await V until M)} = ⌈ cong₂ await_until_ ⌊ sub-id ⌋v ⌊ sub-id-l ⌋m ⌉m
sub-id {TT = ⊢M (match+ V M N)} = ⌈ cong₃ match+ ⌊ sub-id ⌋v ⌊ sub-id-l ⌋m ⌊ sub-id-l ⌋m ⌉m
sub-id {TT = ⊢M (T aT M)} = ⌈ cong₂ _aT_ ⌊ sub-id ⌋t ⌊ sub-id ⌋m ⌉m

sub-id {TT = ⊢T (Tl N)} = ⌈ cong Tl ⌊ sub-id-l ⌋m ⌉t
sub-id {TT = ⊢T (T↓ op V)} = ⌈ cong (T↓ op) ⌊ sub-id ⌋v ⌉t
sub-id {TT = ⊢T Tc} = refl

ren-ren : rename r (rename r' TT) ≡ rename (r ∘ r') TT

ren-ren-var : {Y Z : Type} (x : Y ∈ Γ ∷ Z) → wk₂ r (wk₂ r' x) ≡ wk₂ (r ∘ r') x
ren-ren-var Hd = refl
ren-ren-var (Tl x) = refl

ren-ren-l : rename (wk₂ r) (rename (wk₂ r') TT) ≡ rename (wk₂ (r ∘ r')) TT
ren-ren-l = trans ren-ren (cong-ren ren-ren-var)

ren-ren {TT = ⊢V (` x)} = refl
ren-ren {TT = ⊢V (`` c)} = refl
ren-ren {TT = ⊢V (ƛ M)} = ⌈ cong ƛ ⌊ ren-ren-l ⌋m ⌉v
ren-ren {TT = ⊢V ⟨ V ⟩} = ⌈ cong ⟨_⟩ ⌊ ren-ren ⌋v ⌉v
ren-ren {TT = ⊢V (inl V)} = ⌈ cong inl ⌊ ren-ren ⌋v ⌉v
ren-ren {TT = ⊢V (inr V)} = ⌈ cong inr ⌊ ren-ren ⌋v ⌉v
ren-ren {TT = ⊢V ★} = refl
ren-ren {TT = ⊢V u} = refl

ren-ren {TT = ⊢M (return V)} = ⌈ cong return ⌊ ren-ren ⌋v ⌉m
ren-ren {TT = ⊢M (V · W)} = ⌈ cong₂ _·_ ⌊ ren-ren ⌋v ⌊ ren-ren ⌋v ⌉m
ren-ren {TT = ⊢M (↑ op V M)} = ⌈ cong₂ (↑ op) ⌊ ren-ren ⌋v ⌊ ren-ren ⌋m ⌉m
ren-ren {TT = ⊢M (promise op ↦ M `in N)} = ⌈ cong₂ (promise op ↦_`in_) ⌊ ren-ren-l ⌋m ⌊ ren-ren-l ⌋m ⌉m
ren-ren {TT = ⊢M (await V until M)} = ⌈ cong₂ await_until_ ⌊ ren-ren ⌋v ⌊ ren-ren-l ⌋m ⌉m
ren-ren {TT = ⊢M (match+ V M N)} = ⌈ cong₃ match+ ⌊ ren-ren ⌋v ⌊ ren-ren-l ⌋m ⌊ ren-ren-l ⌋m ⌉m
ren-ren {TT = ⊢M (T aT M)} = ⌈ cong₂ _aT_ ⌊ ren-ren ⌋t ⌊ ren-ren ⌋m ⌉m

ren-ren {TT = ⊢T (Tl N)} = ⌈ cong Tl ⌊ ren-ren-l ⌋m ⌉t
ren-ren {TT = ⊢T (T↓ op V)} = ⌈ cong (T↓ op) ⌊ ren-ren ⌋v ⌉t
ren-ren {TT = ⊢T Tc} = refl

sub-ren : ({Y : Type} (x : Y ∈ Γ) → s' (r x) ≡ V-rename r' (s x)) →
          ------------------------------------------
          rename r TT [ s' ] ≡ rename r' (TT [ s ])

sub-ren-var : ({Y : Type} (x : Y ∈ Γ) → s' (r x) ≡ V-rename r' (s x)) →
              --------------------------------------------------
              ({Y Z : Type} (x : Y ∈ Γ ∷ Z) → lift s' (wk₂ r x) ≡ V-rename (wk₂ r') (lift s x))
sub-ren-var f Hd = refl
sub-ren-var {s' = s'} {r} {r' = r'} {s} H (Tl x) =
  begin
    V-rename Tl (s' (r x))
  ≡⟨ cong (V-rename Tl) (H x) ⟩
    V-rename Tl (V-rename r' (s x))
  ≡⟨ ⌊ ren-ren ⌋v ⟩
    V-rename (Tl ∘ r') (s x)
  ≡⟨ sym ⌊ ren-ren ⌋v ⟩
    V-rename (wk₂ r') (V-rename Tl (s x))
  ∎

sub-ren-l : ({Y : Type} (x : Y ∈ Γ) → s' (r x) ≡ V-rename r' (s x)) →
            --------------------------------------------------------------
            rename (wk₂ r) TT [ lift s' ] ≡ rename (wk₂ r') (TT [ lift s ])
sub-ren-l H = sub-ren (sub-ren-var H) 

sub-ren {TT = ⊢V (` x)} f = ⌈ f x ⌉v
sub-ren {TT = ⊢V (`` c)} f = refl
sub-ren {TT = ⊢V (ƛ M)} f = ⌈ cong ƛ ⌊ sub-ren-l f ⌋m ⌉v
sub-ren {TT = ⊢V ⟨ V ⟩} f = ⌈ cong ⟨_⟩ ⌊ sub-ren {TT = ⊢V V} f ⌋v ⌉v
sub-ren {TT = ⊢V (inl V)} f = ⌈ cong inl ⌊ sub-ren {TT = ⊢V V} f ⌋v ⌉v
sub-ren {TT = ⊢V (inr V)} f = ⌈ cong inr ⌊ sub-ren {TT = ⊢V V} f ⌋v ⌉v
sub-ren {TT = ⊢V ★} f = refl
sub-ren {TT = ⊢V u} f = refl

sub-ren {TT = ⊢M (return V)} f = ⌈ cong return ⌊ sub-ren {TT = ⊢V V} f ⌋v ⌉m
sub-ren {TT = ⊢M (V · W)} f = ⌈ cong₂ _·_ ⌊ sub-ren {TT = ⊢V V} f ⌋v ⌊ sub-ren {TT = ⊢V W} f ⌋v ⌉m
sub-ren {TT = ⊢M (↑ op V M)} f = ⌈ cong₂ (↑ op) ⌊ sub-ren {TT = ⊢V V} f ⌋v ⌊ sub-ren f ⌋m ⌉m
sub-ren {TT = ⊢M (promise op ↦ M `in N)} f = ⌈ cong₂ (promise op ↦_`in_) ⌊ sub-ren-l f ⌋m ⌊ sub-ren-l f ⌋m ⌉m
sub-ren {TT = ⊢M (await V until M)} f = ⌈ cong₂ await_until_ ⌊ sub-ren {TT = ⊢V V} f ⌋v ⌊ sub-ren-l f ⌋m ⌉m
sub-ren {TT = ⊢M (match+ V M N)} f = ⌈ cong₃ match+ ⌊ sub-ren {TT = ⊢V V} f ⌋v ⌊ sub-ren-l f ⌋m ⌊ sub-ren-l f ⌋m ⌉m
sub-ren {TT = ⊢M (T aT M)} f = ⌈ cong₂ _aT_ ⌊ sub-ren f ⌋t ⌊ sub-ren f ⌋m ⌉m

sub-ren {TT = ⊢T (Tl N)} f = ⌈ cong Tl ⌊ sub-ren-l f ⌋m ⌉t
sub-ren {TT = ⊢T (T↓ op V)} f = ⌈ cong (T↓ op) ⌊ sub-ren {TT = ⊢V V} f ⌋v ⌉t
sub-ren {TT = ⊢T Tc} f = refl

sub-sub : TT [ s ] [ s' ] ≡ TT [ _[ s' ]v ∘ s ]

sub-sub-l : TT [ lift s ] [ lift s' ] ≡ TT [ lift (_[ s' ]v ∘ s) ]
sub-sub-l {s = s} = trans sub-sub (cong-sub (λ {Hd → refl; (Tl x) → ⌊ sub-ren {TT = ⊢V (s x)} (λ _ → refl) ⌋v}))

sub-sub {TT = ⊢V (` x)} = refl
sub-sub {TT = ⊢V (`` c)} = refl
sub-sub {TT = ⊢V (ƛ M)} = ⌈ cong ƛ ⌊ sub-sub-l ⌋m ⌉v
sub-sub {TT = ⊢V ⟨ V ⟩} = ⌈ cong ⟨_⟩ ⌊ sub-sub {TT = ⊢V V} ⌋v ⌉v
sub-sub {TT = ⊢V (inl V)} = ⌈ cong inl ⌊ sub-sub {TT = ⊢V V} ⌋v ⌉v
sub-sub {TT = ⊢V (inr V)} = ⌈ cong inr ⌊ sub-sub {TT = ⊢V V} ⌋v ⌉v
sub-sub {TT = ⊢V ★} = refl
sub-sub {TT = ⊢V u} = refl

sub-sub {TT = ⊢M (return V)} = ⌈ cong return ⌊ sub-sub {TT = ⊢V V} ⌋v ⌉m
sub-sub {TT = ⊢M (V · W)} = ⌈ cong₂ _·_ ⌊ sub-sub {TT = ⊢V V} ⌋v ⌊ sub-sub {TT = ⊢V W} ⌋v ⌉m
sub-sub {TT = ⊢M (↑ op V M)} = ⌈ cong₂ (↑ op) ⌊ sub-sub {TT = ⊢V V} ⌋v ⌊ sub-sub ⌋m ⌉m
sub-sub {TT = ⊢M (promise op ↦ M `in N)} = ⌈ cong₂ (promise op ↦_`in_) ⌊ sub-sub-l ⌋m ⌊ sub-sub-l ⌋m ⌉m
sub-sub {TT = ⊢M (await V until M)} = ⌈ cong₂ await_until_ ⌊ sub-sub {TT = ⊢V V} ⌋v ⌊ sub-sub-l ⌋m ⌉m
sub-sub {TT = ⊢M (match+ V M N)} = ⌈ cong₃ match+ ⌊ sub-sub {TT = ⊢V V} ⌋v ⌊ sub-sub-l ⌋m ⌊ sub-sub-l ⌋m ⌉m
sub-sub {TT = ⊢M (T aT M)} = ⌈ cong₂ _aT_ ⌊ sub-sub ⌋t ⌊ sub-sub ⌋m ⌉m

sub-sub {TT = ⊢T (Tl N)} = ⌈ cong Tl ⌊ sub-sub-l ⌋m ⌉t
sub-sub {TT = ⊢T (T↓ op V)} = ⌈ cong (T↓ op) ⌊ sub-sub {TT = ⊢V V} ⌋v ⌉t
sub-sub {TT = ⊢T Tc} = refl

eq₁ : (TT : Γ ⊢ X) (V : Γ ⊢V⦂ Y) →
      ---------------------------
      rename wk₁ TT [ ids [ V ]s ]
      ≡
      TT
eq₁ TT V =
  begin
    rename wk₁ TT [ ids [ V ]s ]
  ≡⟨ sub-ren (λ {Hd → refl; (Tl x) → refl}) ⟩
    rename idr (TT [ ids ])
  ≡⟨ ren-id ⟩
    TT [ ids ]
  ≡⟨ sub-id ⟩
    TT
  ∎

eq₂ : (TT : Γ ∷ X ⊢ Y) (V : Γ' ⊢V⦂ X) →
      ---------------------------
      TT [ lift s ] [ ids [ V ]s ]
      ≡
      TT [ s [ V ]s ]
eq₂ {s = s} TT V =
  begin
    TT [ lift s ] [ ids [ V ]s ]
  ≡⟨ sub-sub ⟩
    TT [ _[ ids [ V ]s ]v ∘ lift s ]
  ≡⟨ cong-sub (λ {Hd → refl; (Tl x) → ⌊ eq₁ _ V ⌋v}) ⟩
    TT [ s [ V ]s ]
  ∎

eq₃ : (s : Sub Γ Γ') (TT : Γ ∷ X ⊢ Y) (V : Γ ⊢V⦂ X) →
      ----------------------
      TT [ ids [ V ]s ] [ s ]
      ≡
      TT [ lift s ] [ ids [ V [ s ]v ]s ]
eq₃ s TT V =
  begin
    TT [ ids [ V ]s ] [ s ]
  ≡⟨ sub-sub ⟩
    TT [ _[ s ]v ∘ (ids [ V ]s) ]
  ≡⟨ cong-sub (λ {Hd → refl; (Tl x) → refl}) ⟩
    TT [ s [ V [ s ]v ]s ]
  ≡⟨ sym (eq₂ TT (V [ s ]v)) ⟩
    TT [ lift s ] [ ids [ V [ s ]v ]s ]
  ∎

eq₄ : (Z : Type) (s : Sub Γ Γ') (TT : Γ ⊢ X) →
      ---------------------------------
      rename (wk₁ {X = Z}) TT [ lift s ]
      ≡
      rename wk₁ (TT [ s ])
eq₄ _ _ _ = sub-ren (λ {Hd → refl; (Tl x) → refl})

eq₅ : (s : Sub Γ Γ') (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A) →
      --------------------------
      strengthen-val V [ s ]v
      ≡
      strengthen-val (V [ lift s ]v)
eq₅ s (` Tl x) with s x
... | ` y = refl
... | `` c = refl
eq₅ s (`` c) = refl

eq₆ : (Z U : Type) (s : Sub Γ Γ') (TT : Γ ⊢ X) →
      ---------------------------------
      rename (wk₁ {X = Z}) (rename (wk₁ {X = U}) TT) [ lift (lift s) ]
      ≡
      rename wk₁ (rename wk₁ (TT [ s ]))
eq₆ _ _ _ _ = trans (eq₄ _ _ _) (cong (rename wk₁) (eq₄ _ _ _))

eq₇ : (TT : Γ ∷ X ⊢ Y) (V : Γ ⊢V⦂ Z) →
       ---------------------------
       rename (wk₂ wk₁) TT [ lift (ids [ V ]s) ]
       ≡
       TT
eq₇ TT V =
  begin
    rename (wk₂ wk₁) TT [ lift (ids [ V ]s) ]
  ≡⟨ sub-ren {TT = TT} (λ {Hd → refl; (Tl x) → refl}) ⟩
    rename idr (TT [ ids ])
  ≡⟨ ren-id ⟩
    TT [ ids ]
  ≡⟨ sub-id ⟩
    TT
  ∎

sub-↝ : (s : Sub Γ Γ') →
        M ↝ M' →
        -------------------
        M [ s ]m ↝ M' [ s ]m
sub-↝ s (apply M V) rewrite ⌊ eq₃ s (⊢M M) V ⌋m = apply _ _
sub-↝ s (let-return V N) rewrite ⌊ eq₃ s (⊢M N) V ⌋m = let-return _ _
sub-↝ s (T-↑ V T M) = T-↑ _ _ _
sub-↝ s (T-promise {X = X} T M N)  rewrite ⌊ eq₄ ⟨ X ⟩ s (⊢T T) ⌋t = T-promise _ _ _
sub-↝ s (T-await {X = X} T V M) rewrite ⌊ eq₄ X s (⊢T T) ⌋t = T-await _ _ _
sub-↝ s (promise-↑ V M N) rewrite eq₅ s V = promise-↑ _ _ _
sub-↝ s (↓-return V W) = ↓-return _ _
sub-↝ s (↓-promise-op {X = X} V M N)
  rewrite
  ⌊ eq₃ s (⊢M M) V ⌋m |
  ⌊ eq₄ ⟨ X ⟩ s (⊢T (T↓ _ V)) ⌋t |
  ⌊ eq₆ 𝟙 (⟨ X ⟩ + 𝟙) s (⊢M (promise _ ↦ M `in return (` Hd))) ⌋m
  = ↓-promise-op (V [ s ]v) (M [ lift s ]m) (N [ lift s ]m)
sub-↝ s (await-promise V M) rewrite ⌊ eq₃ s (⊢M M) V ⌋m = await-promise _ _
sub-↝ s (match+-inl V M N) rewrite ⌊ eq₃ s (⊢M M) V ⌋m = match+-inl _ _ _
sub-↝ s (match+-inr V M N) rewrite ⌊ eq₃ s (⊢M N) V ⌋m = match+-inr _ _ _
sub-↝ s (↑-discard V) = ↑-discard _
sub-↝ s (context-↑ r) = context-↑ (sub-↝ s r)
sub-↝ s (context-promise r) = context-promise (sub-↝ (lift s) r)
sub-↝ s (context-T T r) = context-T _ (sub-↝ s r)
sub-↝ s (coerce-return V) = coerce-return _