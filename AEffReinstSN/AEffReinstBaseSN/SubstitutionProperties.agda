-- the code in this file is adapted from Programming Language Foundations in Agda, available under the CC BY 4.0 license
-- https://plfa.inf.ed.ac.uk/20.07/Substitution/
-- https://creativecommons.org/licenses/by/4.0/deed.en

{-# OPTIONS --guardedness #-}

open import AEffReinstSN.AEffReinstBaseSN.AEff

open import Data.List using ([]) renaming (_∷_ to _∷ₗ_)
open import Data.Product using (Σ-syntax; _,_; _×_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂; sym; trans)

open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_)

module AEffReinstSN.AEffReinstBaseSN.SubstitutionProperties where

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
cong₃ f refl refl refl = refl


-- POINTWISE EQUALITY OF RENAMINGS

infix 4 _≈ᵣ_
_≈ᵣ_ : Ren Γ Γ' → Ren Γ Γ' → Set
r ≈ᵣ r' = {Y : Type} (x : Y ∈ _) → r x ≡ r' x


-- POINTWISE EQUALITY OF SUBSTITUTIONS

infix 4 _≈ₛ_
_≈ₛ_ : Sub Γ Γ' → Sub Γ Γ' → Set
s ≈ₛ s' = {Y : Type} (x : Y ∈ _) → s x ≡ s' x


-- ACTION OF POINTWISE EQUAL RENAMINGS RESULTS IN EQUAL TERMS

cong-ren-v : r ≈ᵣ r' → V-rename r V ≡ V-rename r' V

cong-ren-m : r ≈ᵣ r' → M-rename r M ≡ M-rename r' M

cong-ren-l : r ≈ᵣ r' → M-rename (wk₂ r) M ≡ M-rename (wk₂ r') M

cong-ren-l f = cong-ren-m (λ {Hd → refl; (Tl x) → cong Tl (f x)})

cong-ren-v {V = ` x} f = cong `_ (f x)
cong-ren-v {V = `` c} f = refl
cong-ren-v {V = ƛ M} f = cong ƛ (cong-ren-l f)
cong-ren-v {V = ⟨ V ⟩} f = cong ⟨_⟩ (cong-ren-v f)
cong-ren-v {V = inl V} f = cong inl (cong-ren-v f)
cong-ren-v {V = inr V} f = cong inr (cong-ren-v f)
cong-ren-v {V = ★} f = refl

cong-ren-m {M = return V} f = cong return (cong-ren-v f)
cong-ren-m {M = V · W} f = cong₂ _·_ (cong-ren-v f) (cong-ren-v f)
cong-ren-m {M = let= M `in N} f = cong₂ let=_`in_ (cong-ren-m f) (cong-ren-l f)
cong-ren-m {M = ↑ op V M} f = cong₂ (↑ op) (cong-ren-v f) (cong-ren-m f)
cong-ren-m {M = ↓ op V M} f = cong₂ (↓ op) (cong-ren-v f) (cong-ren-m f)
cong-ren-m {M = promise op ↦ M `in N} f = cong₂ (promise op ↦_`in_) (cong-ren-l f) (cong-ren-l f)
cong-ren-m {M = await V until M} f = cong₂ await_until_ (cong-ren-v f) (cong-ren-l f)
cong-ren-m {M = match+ V M N} f = cong₃ match+ (cong-ren-v f) (cong-ren-l f) (cong-ren-l f)


-- ACTION OF POINTWISE EQUAL SUBSTITUTIONS RESULTS IN EQUAL TERMS

cong-sub-v : s ≈ₛ s' → V [ s ]v ≡ V [ s' ]v

cong-sub-m : s ≈ₛ s' → M [ s ]m ≡ M [ s' ]m

cong-sub-l : s ≈ₛ s' → M [ lift s ]m ≡ M [ lift s' ]m

cong-sub-l f = cong-sub-m (λ {Hd → refl; (Tl x) → cong (V-rename Tl) (f x)})

cong-sub-v {V = ` x} f = f x
cong-sub-v {V = `` c} f = refl
cong-sub-v {V = ƛ M} f = cong ƛ (cong-sub-l f)
cong-sub-v {V = ⟨ V ⟩} f = cong ⟨_⟩ (cong-sub-v {V = V} f)
cong-sub-v {V = inl V} f = cong inl (cong-sub-v {V = V} f)
cong-sub-v {V = inr V} f = cong inr (cong-sub-v {V = V} f)
cong-sub-v {V = ★} f = refl

cong-sub-m {M = return V} f = cong return (cong-sub-v {V = V} f)
cong-sub-m {M = V · W} f = cong₂ _·_ (cong-sub-v {V = V} f) (cong-sub-v {V = W} f)
cong-sub-m {M = let= M `in N} f = cong₂ let=_`in_ (cong-sub-m f) (cong-sub-l f)
cong-sub-m {M = ↑ op V M} f = cong₂ (↑ op) (cong-sub-v {V = V} f) (cong-sub-m f)
cong-sub-m {M = ↓ op V M} f = cong₂ (↓ op) (cong-sub-v {V = V} f) (cong-sub-m f)
cong-sub-m {M = promise op ↦ M `in N} f = cong₂ (promise op ↦_`in_) (cong-sub-l f) (cong-sub-l f)
cong-sub-m {M = await V until M} f = cong₂ await_until_ (cong-sub-v {V = V} f) (cong-sub-l f)
cong-sub-m {M = match+ V M N} f = cong₃ match+ (cong-sub-v {V = V} f) (cong-sub-l f) (cong-sub-l f)


-- ACTION OF IDENTITY RENAMINGS LEAVES THE TERM UNCHANGED

ren-id-v : V-rename id-ren V ≡ V

ren-id-m : M-rename id-ren M ≡ M

ren-id-l : M-rename (wk₂ id-ren) M ≡ M

ren-id-l = trans (cong-ren-m (λ {Hd → refl; (Tl x) → refl})) ren-id-m

ren-id-v {V = ` x} = refl
ren-id-v {V = `` c} = refl
ren-id-v {V = ƛ M} = cong ƛ ren-id-l
ren-id-v {V = ⟨ V ⟩} = cong ⟨_⟩ ren-id-v
ren-id-v {V = inl V} = cong inl ren-id-v
ren-id-v {V = inr V} = cong inr ren-id-v
ren-id-v {V = ★} = refl

ren-id-m {M = return V} = cong return ren-id-v
ren-id-m {M = V · W} = cong₂ _·_ ren-id-v ren-id-v
ren-id-m {M = let= M `in N} = cong₂ let=_`in_ ren-id-m ren-id-l
ren-id-m {M = ↑ op V M} = cong₂ (↑ op) ren-id-v ren-id-m
ren-id-m {M = ↓ op V M} = cong₂ (↓ op) ren-id-v ren-id-m
ren-id-m {M = promise op ↦ M `in N} = cong₂ (promise op ↦_`in_) ren-id-l ren-id-l
ren-id-m {M = await V until M} = cong₂ await_until_ ren-id-v ren-id-l
ren-id-m {M = match+ V M N} = cong₃ match+ ren-id-v ren-id-l ren-id-l


-- ACTION OF IDENTITY SUBSTITUTIONS LEAVES THE TERM UNCHANGED

sub-id-v : V [ id-subst ]v ≡ V

sub-id-m : M [ id-subst ]m ≡ M

sub-id-l : M [ lift id-subst ]m ≡ M

sub-id-l = trans (cong-sub-m (λ {Hd → refl; (Tl x) → refl})) sub-id-m

sub-id-v {V = ` x} = refl
sub-id-v {V = `` c} = refl
sub-id-v {V = ƛ M} = cong ƛ sub-id-l
sub-id-v {V = ⟨ V ⟩} = cong ⟨_⟩ (sub-id-v {V = V})
sub-id-v {V = inl V} = cong inl sub-id-v
sub-id-v {V = inr V} = cong inr sub-id-v
sub-id-v {V = ★} = refl

sub-id-m {M = return V} = cong return (sub-id-v {V = V})
sub-id-m {M = V · W} = cong₂ _·_ (sub-id-v {V = V}) (sub-id-v {V = W})
sub-id-m {M = let= M `in N} = cong₂ let=_`in_ sub-id-m sub-id-l
sub-id-m {M = ↑ op V M} = cong₂ (↑ op) (sub-id-v {V = V}) sub-id-m
sub-id-m {M = ↓ op V M} = cong₂ (↓ op) (sub-id-v {V = V}) sub-id-m
sub-id-m {M = promise op ↦ M `in N} = cong₂ (promise op ↦_`in_) sub-id-l sub-id-l
sub-id-m {M = await V until M} = cong₂ await_until_ (sub-id-v {V = V}) sub-id-l
sub-id-m {M = match+ V M N} = cong₃ match+ sub-id-v sub-id-l sub-id-l


-- ACTION OF A COMPOSITION OF RENAMINGS IS THE SAME AS PERFORMING THE RENAMINGS ONE AFTER THE OTHER

ren-ren-v : V-rename r (V-rename r' V) ≡ V-rename (r ∘ r') V

ren-ren-m : M-rename r (M-rename r' M) ≡ M-rename (r ∘ r') M

ren-ren-l : M-rename (wk₂ r) (M-rename (wk₂ r') M) ≡ M-rename (wk₂ (r ∘ r')) M

ren-ren-l = trans ren-ren-m (cong-ren-m (λ {Hd → refl; (Tl x) → refl}))

ren-ren-v {V = ` x} = refl
ren-ren-v {V = `` c} = refl
ren-ren-v {V = ƛ M} = cong ƛ ren-ren-l
ren-ren-v {V = ⟨ V ⟩} = cong ⟨_⟩ ren-ren-v
ren-ren-v {V = inl V} = cong inl ren-ren-v
ren-ren-v {V = inr V} = cong inr ren-ren-v
ren-ren-v {V = ★} = refl

ren-ren-m {M = return V} = cong return ren-ren-v
ren-ren-m {M = V · W} = cong₂ _·_ ren-ren-v ren-ren-v
ren-ren-m {M = let= M `in N} = cong₂ let=_`in_ ren-ren-m ren-ren-l
ren-ren-m {M = ↑ op V M} = cong₂ (↑ op) ren-ren-v ren-ren-m
ren-ren-m {M = ↓ op V M} = cong₂ (↓ op) ren-ren-v ren-ren-m
ren-ren-m {M = promise op ↦ M `in N} = cong₂ (promise op ↦_`in_) ren-ren-l ren-ren-l
ren-ren-m {M = await V until M} = cong₂ await_until_ ren-ren-v ren-ren-l
ren-ren-m {M = match+ V M N} = cong₃ match+ ren-ren-v ren-ren-l ren-ren-l


-- A RENAMING AND SUBSTITUTION THAT COMMUTE ON VARIABLES ALSO COMMUTE ON TERMS

sub-ren-var : s' ∘ r ≈ₛ V-rename r' ∘ s → lift {X = X} s' ∘ wk₂ r ≈ₛ V-rename (wk₂ r') ∘ lift s
sub-ren-var f Hd = refl
sub-ren-var f (Tl x) rewrite f x = trans ren-ren-v (sym ren-ren-v)

sub-ren-v : s' ∘ r ≈ₛ V-rename r' ∘ s → V-rename r V [ s' ]v ≡ V-rename r' (V [ s ]v)

sub-ren-m : s' ∘ r ≈ₛ V-rename r' ∘ s → M-rename r M [ s' ]m ≡ M-rename r' (M [ s ]m)

sub-ren-l : s' ∘ r ≈ₛ V-rename r' ∘ s → M-rename (wk₂ r) M [ lift s' ]m ≡ M-rename (wk₂ r') (M [ lift s ]m)

sub-ren-l f = sub-ren-m (sub-ren-var f)

sub-ren-v {V = ` x} f = f x
sub-ren-v {V = `` c} f = refl
sub-ren-v {V = ƛ M} f = cong ƛ (sub-ren-l f)
sub-ren-v {V = ⟨ V ⟩} f = cong ⟨_⟩ (sub-ren-v {V = V} f)
sub-ren-v {V = inl V} f = cong inl (sub-ren-v {V = V} f)
sub-ren-v {V = inr V} f = cong inr (sub-ren-v {V = V} f)
sub-ren-v {V = ★} f = refl

sub-ren-m {M = return V} f = cong return (sub-ren-v {V = V} f)
sub-ren-m {M = V · W} f = cong₂ _·_ (sub-ren-v {V = V} f) (sub-ren-v {V = W} f)
sub-ren-m {M = let= M `in N} f = cong₂ let=_`in_ (sub-ren-m f) (sub-ren-l f)
sub-ren-m {M = ↑ op V M} f = cong₂ (↑ op) (sub-ren-v {V = V} f) (sub-ren-m f)
sub-ren-m {M = ↓ op V M} f = cong₂ (↓ op) (sub-ren-v {V = V} f) (sub-ren-m f)
sub-ren-m {M = promise op ↦ M `in N} f = cong₂ (promise op ↦_`in_) (sub-ren-l f) (sub-ren-l f)
sub-ren-m {M = await V until M} f = cong₂ await_until_ (sub-ren-v {V = V} f) (sub-ren-l f)
sub-ren-m {M = match+ V M N} f = cong₃ match+ (sub-ren-v {V = V} f) (sub-ren-l f) (sub-ren-l f)


-- COMPOSITION OF SUBSTITUTIONS

infixr 9 _⨟_
_⨟_ : Sub Γ Γ' → Sub Γ' Γ'' → Sub Γ Γ''
(s ⨟ s') x = s x [ s' ]v


-- LIFTING A COMPOSITION OF SUBSTITUTIONS IS POINTWISE EQUAL TO A COMPOSITION OF LIFTED SUBSTITUTIONS

lift-⨟ : lift {X = X} s ⨟ lift s' ≈ₛ lift (s ⨟ s')
lift-⨟ Hd = refl
lift-⨟ {s = s} (Tl x) = sub-ren-v {V = s x} (λ _ → refl)


-- ACTION OF A COMPOSITION OF SUBSTITUTIONS IS THE SAME AS PERFORMING THE SUBSTITUTIONS ONE AFTER THE OTHER

sub-sub-v : V [ s ]v [ s' ]v ≡ V [ s ⨟ s' ]v

sub-sub-m : M [ s ]m [ s' ]m ≡ M [ s ⨟ s' ]m

sub-sub-l : M [ lift s ]m [ lift s' ]m ≡ M [ lift (s ⨟ s') ]m

sub-sub-l {s = s} = trans sub-sub-m (cong-sub-m (λ {Hd → refl; (Tl x) → sub-ren-v {V = s x} (λ _ → refl)}))

sub-sub-v {V = ` x} = refl
sub-sub-v {V = `` c} = refl
sub-sub-v {V = ƛ M} = cong ƛ sub-sub-l
sub-sub-v {V = ⟨ V ⟩} = cong ⟨_⟩ (sub-sub-v {V = V})
sub-sub-v {V = inl V} = cong inl (sub-sub-v {V = V})
sub-sub-v {V = inr V} = cong inr (sub-sub-v {V = V})
sub-sub-v {V = ★} = refl

sub-sub-m {M = return V} = cong return (sub-sub-v {V = V})
sub-sub-m {M = V · W} = cong₂ _·_ (sub-sub-v {V = V}) (sub-sub-v {V = W})
sub-sub-m {M = let= M `in N} = cong₂ let=_`in_ sub-sub-m sub-sub-l
sub-sub-m {M = ↑ op V M} = cong₂ (↑ op) (sub-sub-v {V = V}) sub-sub-m
sub-sub-m {M = ↓ op V M} = cong₂ (↓ op) (sub-sub-v {V = V}) sub-sub-m
sub-sub-m {M = promise op ↦ M `in N} = cong₂ (promise op ↦_`in_) sub-sub-l sub-sub-l
sub-sub-m {M = await V until M} = cong₂ await_until_ (sub-sub-v {V = V}) sub-sub-l
sub-sub-m {M = match+ V M N} = cong₃ match+ (sub-sub-v {V = V}) sub-sub-l sub-sub-l


-- VARIOUS IDENTITIES INVOLVING RENAMINGS AND SUBSTITUTIONS

wk₁V[id-subst[W]] : (V : Γ ⊢V⦂ X) (W : Γ ⊢V⦂ Y) →
                    ---------------------------
                    V
                    ≡
                    V-rename wk₁ V [ id-subst [ W ]s ]v

wk₁V[id-subst[W]] V W =
  begin
    V
  ≡⟨ sym sub-id-v ⟩
    V [ id-subst ]v
  ≡⟨ sym ren-id-v ⟩
    V-rename id-ren (V [ id-subst ]v)
  ≡⟨ sym (sub-ren-v {V = V} (λ _ → refl)) ⟩
    V-rename wk₁ V [ id-subst [ W ]s ]v
  ∎

wk₂wk₁M[liftid-subst[W]] : (M : Γ ∷ Z ⊢M⦂ X) (W : Γ ⊢V⦂ Y) →
                           ---------------------------
                           M
                           ≡
                           M-rename (wk₂ wk₁) M [ lift (id-subst [ W ]s) ]m

wk₂wk₁M[liftid-subst[W]] M W =
  begin
    M
  ≡⟨ sym sub-id-m ⟩
    M [ id-subst ]m
  ≡⟨ sym ren-id-m ⟩
    M-rename id-ren (M [ id-subst ]m)
  ≡⟨ sym (sub-ren-m {M = M} (λ {Hd → refl; (Tl x) → refl})) ⟩
    M-rename (wk₂ wk₁) M [ lift (id-subst [ W ]s) ]m
  ∎

M[lifts][id-subst[V]] : (M : Γ ∷ X ⊢M⦂ Y) (V : Γ' ⊢V⦂ X) →
                        -----------------------------
                        M [ s [ V ]s ]m
                        ≡
                        M [ lift s ]m [ id-subst [ V ]s ]m

M[lifts][id-subst[V]] {s = s} M V =
  begin
    M [ s [ V ]s ]m
  ≡⟨ cong-sub-m (λ {Hd → refl; (Tl x) → wk₁V[id-subst[W]] _ V}) ⟩
    M [ lift s ⨟ id-subst [ V ]s ]m
  ≡⟨ sym sub-sub-m ⟩
    M [ lift s ]m [ id-subst [ V ]s ]m
  ∎

M[id-subst[V]][s] : (s : Sub Γ Γ') (M : Γ ∷ X ⊢M⦂ Y) (V : Γ ⊢V⦂ X) →
                    -----------------------
                    M [ id-subst [ V ]s ]m [ s ]m
                    ≡
                    M [ lift s ]m [ id-subst [ V [ s ]v ]s ]m

M[id-subst[V]][s] s M V =
  begin
    M [ id-subst [ V ]s ]m [ s ]m
  ≡⟨ sub-sub-m ⟩
    M [ id-subst [ V ]s ⨟ s ]m
  ≡⟨ cong-sub-m (λ {Hd → refl; (Tl x) → refl}) ⟩
    M [ s [ V [ s ]v ]s ]m
  ≡⟨ M[lifts][id-subst[V]] M (V [ s ]v) ⟩
    M [ lift s ]m [ id-subst [ V [ s ]v ]s ]m
  ∎

wk₁[V[s]] : (Z : Type) (s : Sub Γ Γ') (V : Γ ⊢V⦂ X) →
            ---------------------------------
            V-rename (wk₁ {X = Z}) V [ lift s ]v
            ≡
            V-rename wk₁ (V [ s ]v)

wk₁[V[s]] _ _ V = sub-ren-v {V = V} (λ _ → refl)

wk₁[M[s]] : (Z : Type) (s : Sub Γ Γ') (M : Γ ⊢M⦂ X) →
            ---------------------------------
            M-rename (wk₁ {X = Z}) M [ lift s ]m
            ≡
            M-rename wk₁ (M [ s ]m)

wk₁[M[s]] _ _ M = sub-ren-m {M = M} (λ _ → refl)

wk₂wk₁[M[lifts]] : (Z : Type) (s : Sub Γ Γ') (M : Γ ∷ X ⊢M⦂ Y) →
                   ----------------------------------------------
                   M-rename (wk₂ (wk₁ {X = Z})) M [ lift (lift s) ]m
                   ≡
                   M-rename (wk₂ wk₁) (M [ lift s ]m)

wk₂wk₁[M[lifts]] _ _ _ = sub-ren-l (λ _ → refl)

wk₁wk₁M[s] : (Z U : Type) (s : Sub Γ Γ') (M : Γ ⊢M⦂ X) →
             -----------------------------------------------
             M-rename (wk₁ {X = Z}) (M-rename (wk₁ {X = U}) M) [ lift (lift s) ]m
             ≡
             M-rename wk₁ (M-rename wk₁ (M [ s ]m))

wk₁wk₁M[s] _ _ _ _ = trans (wk₁[M[s]] _ _ _) (cong (M-rename wk₁) (wk₁[M[s]] _ _ _))

wk₂wk₁V[Hd] : V
              ≡
              V-rename (wk₂ wk₁) V [ id-subst [ ` Hd ]s ]v

wk₂wk₁V[Hd] {V = V} = sym (trans (sub-ren-v {V = V} (λ {Hd → refl; (Tl x) → refl})) (trans ren-id-v sub-id-v))

wk₂wk₁M[Hd] : M
              ≡
              M-rename (wk₂ wk₁) M [ id-subst [ ` Hd ]s ]m

wk₂wk₁M[Hd] {M = M} = sym (trans (sub-ren-m {M = M} (λ {Hd → refl; (Tl x) → refl})) (trans ren-id-m sub-id-m))

wk₂r[wk₂r'[wk₁V]] : V-rename (wk₁ {X = X}) (V-rename r (V-rename r' V))
                    ≡
                    V-rename (wk₂ r) (V-rename (wk₂ r') (V-rename wk₁ V))

wk₂r[wk₂r'[wk₁V]] =
  trans ren-ren-v
  (trans ren-ren-v
  (trans (cong-ren-v (λ {Hd → refl; (Tl x) → refl}))
  (trans (sym ren-ren-v)
  (sym ren-ren-v))))

m-ren-lemma-big :
  M-rename (wk₂ (wk₂ r))
    (M-rename (wk₂ (wk₂ (wk₂ r')))
      (M-rename (wk₂ wk₁) (M-rename (wk₂ wk₁) M))
    [ lift (lift (id-subst [ V ]s)) ]m)
  [ lift (id-subst [ V' ]s) ]m
  ≡
  M-rename (wk₂ r) (M-rename (wk₂ r') M)

m-ren-lemma-big =
  trans (cong (λ z → M-rename _ (z [ _ ]m) [ _ ]m) (trans (trans ren-ren-l ren-ren-l) (sym (trans ren-ren-l ren-ren-l))))
  (trans (cong (λ z → M-rename _ z [ _ ]m) (wk₂wk₁[M[lifts]] _ _ _))
  (trans (cong (λ z → M-rename _ (M-rename (wk₂ wk₁) z) [ _ ]m) (sym (wk₂wk₁M[liftid-subst[W]] _ _)))
  (trans (cong (_[ _ ]m) (trans ren-ren-l (sym ren-ren-l)))
  (sym (wk₂wk₁M[liftid-subst[W]] _ _)))))

strengthenV[lifts] : (s : Sub Γ Γ') (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A) →
                     --------------------------
                     strengthen-val V [ s ]v
                     ≡
                     strengthen-val (V [ lift s ]v)

strengthenV[lifts] s (` Tl x) with s x
... | ` y = refl
... | `` c = refl
strengthenV[lifts] s (`` c) = refl

ren-strengthenV : (r : Ren Γ Γ') (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A) →
                  --------------------------
                  V-rename r (strengthen-val V)
                  ≡
                  strengthen-val (V-rename (wk₂ r) V)

ren-strengthenV r (` Tl x) = refl
ren-strengthenV r (`` c) = refl


-- STABILITY OF REDUCTIONS UNDER SUBSTITUTION

sub-↝↝ : (s : Sub Γ Γ') → M ↝↝ M' → M [ s ]m ↝↝ M' [ s ]m

sub-↝↝ s (apply M V) rewrite M[id-subst[V]][s] s M V = apply _ _
sub-↝↝ s (let-return V N) rewrite M[id-subst[V]][s] s N V = let-return _ _
sub-↝↝ s (let-↑ N T M) = let-↑ _ _ _
sub-↝↝ s (↓-↑ W T M) = ↓-↑ _ _ _
sub-↝↝ s (promise-↑ V M N) rewrite strengthenV[lifts] s V = promise-↑ _ _ _
sub-↝↝ s (↓-return V W) = ↓-return _ _
sub-↝↝ s (let-promise {X = X} L M N) rewrite wk₂wk₁[M[lifts]] ⟨ X ⟩ s L = let-promise _ _ _
sub-↝↝ s (↓-promise-op {X = X} V M N)
  rewrite
  M[id-subst[V]][s] s M V |
  wk₁[V[s]] ⟨ X ⟩ s V |
  wk₁wk₁M[s] 𝟙 (⟨ X ⟩ + 𝟙) s (promise _ ↦ M `in return (` Hd)) =
  ↓-promise-op _ _ _
sub-↝↝ s (↓-promise-op' {X = X} p V M N) rewrite wk₁[V[s]] ⟨ X ⟩ s V = ↓-promise-op' p _ _ _
sub-↝↝ s (let-await {X = X} N V M) rewrite wk₂wk₁[M[lifts]] X s N = let-await _ _ _
sub-↝↝ s (↓-await {X = X} W V M) rewrite wk₁[V[s]] X s W = ↓-await _ _ _
sub-↝↝ s (await-promise V M) rewrite M[id-subst[V]][s] s M V = await-promise _ _
sub-↝↝ s (match+-inl V M N) rewrite M[id-subst[V]][s] s M V = match+-inl _ _ _
sub-↝↝ s (match+-inr V M N) rewrite M[id-subst[V]][s] s N V = match+-inr _ _ _
sub-↝↝ s (context-↑ r) = context-↑ (sub-↝↝ s r)
sub-↝↝ s (context-promise r) = context-promise (sub-↝↝ (lift s) r)
sub-↝↝ s (context-let r) = context-let (sub-↝↝ s r)
sub-↝↝ s (context-↓ r) = context-↓ (sub-↝↝ s r)


-- EACH RENAMING IS ALSO A SUBSTITUTION

ren : Ren Γ Γ' → Sub Γ Γ'
ren r x = ` r x

ren-rename-v : V [ ren r ]v ≡ V-rename r V

ren-rename-m : M [ ren r ]m ≡ M-rename r M

ren-rename-l : M [ lift (ren r) ]m ≡ M-rename (wk₂ r) M

ren-rename-l = trans (cong-sub-m (λ {Hd → refl; (Tl x) → refl})) ren-rename-m

ren-rename-v {V = ` x} = refl
ren-rename-v {V = `` c} = refl
ren-rename-v {V = ƛ M} = cong ƛ ren-rename-l
ren-rename-v {V = ⟨ V ⟩} = cong ⟨_⟩ ren-rename-v
ren-rename-v {V = inl V} = cong inl ren-rename-v
ren-rename-v {V = inr V} = cong inr ren-rename-v
ren-rename-v {V = ★} = refl

ren-rename-m {M = return V} = cong return ren-rename-v
ren-rename-m {M = V · W} = cong₂ _·_ ren-rename-v ren-rename-v
ren-rename-m {M = let= M `in N} = cong₂ let=_`in_ ren-rename-m ren-rename-l
ren-rename-m {M = ↑ op V M} = cong₂ (↑ op) ren-rename-v ren-rename-m
ren-rename-m {M = ↓ op V M} = cong₂ (↓ op) ren-rename-v ren-rename-m
ren-rename-m {M = promise op ↦ M `in N} = cong₂ (promise op ↦_`in_) ren-rename-l ren-rename-l
ren-rename-m {M = await V until M} = cong₂ await_until_ ren-rename-v ren-rename-l
ren-rename-m {M = match+ V M N} = cong₃ match+ ren-rename-v ren-rename-l ren-rename-l


-- STABILITY OF REDUCTIONS UNDER RENAMING

ren-↝↝ : (r : Ren Γ Γ') → M ↝↝ M' → M-rename r M ↝↝ M-rename r M'

ren-↝↝ {M = M} {M' = M'} rn r
  rewrite
  sym (ren-rename-m {M = M} {r = rn}) |
  sym (ren-rename-m {M = M'} {r = rn}) =
  sub-↝↝ _ r
  

-- UNUSED VARIABLES IN A COMPUTATION STAY UNUSED IN ALL OF ITS REDUCTS

ren-↝↝-Σ : (r : Ren Γ Γ') →
           M-rename r M ↝↝ M' →
           -------------------------------------------
           Σ[ M'' ∈ _ ] M' ≡ M-rename r M'' × M ↝↝ M''

ren-↝↝-Σ {M = ƛ _ · _} r (apply _ _) = _ , sub-ren-m (λ {Hd → refl; (Tl x₂) → refl}) , apply _ _
ren-↝↝-Σ {M = let= return _ `in _} r (let-return _ _) = _ , sub-ren-m (λ {Hd → refl; (Tl x₂) → refl}) , let-return _ _
ren-↝↝-Σ {M = let= _ · _ `in _} r (context-let r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-let e'
ren-↝↝-Σ {M = let= let= _ `in _ `in _} r (context-let r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-let e'
ren-↝↝-Σ {M = let= ↑ _ _ _ `in _} r (let-↑ _ _ _) = _ , refl , let-↑ _ _ _
ren-↝↝-Σ {M = let= ↑ _ _ _ `in _} r (context-let r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-let e'
ren-↝↝-Σ {M = let= ↓ _ _ _ `in _} r (context-let r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-let e'
ren-↝↝-Σ {M = let= promise _ ↦ _ `in _ `in _} r (let-promise L M₃ N) =
  _ , cong (λ z → promise _ ↦ _ `in let= _ `in z) (trans ren-ren-l (sym ren-ren-l)) , let-promise _ _ _
ren-↝↝-Σ {M = let= promise _ ↦ _ `in _ `in _} r (context-let r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-let e'
ren-↝↝-Σ {M = let= await _ until _ `in _} r (let-await N V M₂) =
  _ , cong (λ z → await _ until (let= _ `in z)) (trans ren-ren-l (sym ren-ren-l)) , let-await _ _ _
ren-↝↝-Σ {M = let= await _ until _ `in _} r (context-let r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-let e'
ren-↝↝-Σ {M = let= match+ _ _ _ `in _} r (context-let r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-let e'
ren-↝↝-Σ {M = ↑ _ _ _} r (context-↑ r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-↑ e'
ren-↝↝-Σ {M = ↓ _ _ (return _)} r (↓-return _ _) = _ , refl , ↓-return _ _
ren-↝↝-Σ {M = ↓ _ _ (_ · _)} r (context-↓ r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-↓ e'
ren-↝↝-Σ {M = ↓ _ _ (let= _ `in _)} r (context-↓ r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-↓ e'
ren-↝↝-Σ {M = ↓ _ _ (↑ _ _ _)} r (↓-↑ _ _ _) = _ , refl , ↓-↑ _ _ _
ren-↝↝-Σ {M = ↓ _ _ (↑ _ _ _)} r (context-↓ r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-↓ e'
ren-↝↝-Σ {M = ↓ _ _ (↓ _ _ _)} r (context-↓ r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-↓ e'
ren-↝↝-Σ {M = ↓ _ _ (promise _ ↦ _ `in _)} r (↓-promise-op V M₂ N) =
  _ ,
  cong₃
    (λ z w u → let= let= z `in match+ _ _ (promise _ ↦ w `in _) `in ↓ _ u _)
    (sub-ren-m (λ {Hd → refl; (Tl x₂) → refl}))
    (trans ren-ren-l (trans ren-ren-l (sym (trans ren-ren-l ren-ren-l))))
    (trans ren-ren-v (sym ren-ren-v)) ,
  ↓-promise-op _ _ _
ren-↝↝-Σ {M = ↓ _ _ (promise _ ↦ _ `in _)} r (↓-promise-op' p V M₂ N) =
  _ , cong (λ z → promise _ ↦ _ `in ↓ _ z _) (trans ren-ren-v (sym ren-ren-v)) , ↓-promise-op' p _ _ _
ren-↝↝-Σ {M = ↓ _ _ (promise _ ↦ _ `in _)} r (context-↓ r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-↓ e'
ren-↝↝-Σ {M = ↓ _ _ (await _ until _)} r (↓-await _ _ _) = _ , cong (λ z → await _ until ↓ _ z _) (trans ren-ren-v (sym ren-ren-v)) , ↓-await _ _ _
ren-↝↝-Σ {M = ↓ _ _ (await _ until _)} r (context-↓ r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-↓ e'
ren-↝↝-Σ {M = ↓ _ _ (match+ _ _ _)} r (context-↓ r') with ren-↝↝-Σ r r'
... | _ , refl , e' = _ , refl , context-↓ e'
ren-↝↝-Σ {M = promise _ ↦ _ `in return _} r (context-promise r') with ren-↝↝-Σ (wk₂ r) r'
... | _ , refl , e' = _ , refl , context-promise e'
ren-↝↝-Σ {M = promise _ ↦ _ `in (_ · _)} r (context-promise r') with ren-↝↝-Σ (wk₂ r) r'
... | _ , refl , e' = _ , refl , context-promise e'
ren-↝↝-Σ {M = promise _ ↦ _ `in (let= _ `in _)} r (context-promise r') with ren-↝↝-Σ (wk₂ r) r'
... | _ , refl , e' = _ , refl , context-promise e'
ren-↝↝-Σ {M = promise _ ↦ _ `in ↑ _ _ _} r (promise-↑ V M₂ N) = _ , cong (λ z → ↑ _ z _) (sym (ren-strengthenV _ _)) , promise-↑ _ _ _
ren-↝↝-Σ {M = promise _ ↦ _ `in ↑ _ _ _} r (context-promise r') with ren-↝↝-Σ (wk₂ r) r'
... | _ , refl , e' = _ , refl , context-promise e'
ren-↝↝-Σ {M = promise _ ↦ _ `in ↓ _ _ _} r (context-promise r') with ren-↝↝-Σ (wk₂ r) r'
... | _ , refl , e' = _ , refl , context-promise e'
ren-↝↝-Σ {M = promise _ ↦ _ `in (promise _ ↦ _ `in _)} r (context-promise r') with ren-↝↝-Σ (wk₂ r) r'
... | _ , refl , e' = _ , refl , context-promise e'
ren-↝↝-Σ {M = promise _ ↦ _ `in (await _ until _)} r (context-promise r') with ren-↝↝-Σ (wk₂ r) r'
... | _ , refl , e' = _ , refl , context-promise e'
ren-↝↝-Σ {M = promise _ ↦ _ `in match+ _ _ _} r (context-promise r') with ren-↝↝-Σ (wk₂ r) r'
... | _ , refl , e' = _ , refl , context-promise e'
ren-↝↝-Σ {M = await ⟨ _ ⟩ until _} r (await-promise _ _) = _ , sub-ren-m (λ {Hd → refl; (Tl x₂) → refl}) , await-promise _ _
ren-↝↝-Σ {M = match+ (inl _) _ _} r (match+-inl _ _ _) = _ , sub-ren-m (λ {Hd → refl; (Tl x₂) → refl}) , match+-inl _ _ _
ren-↝↝-Σ {M = match+ (inr _) _ _} r (match+-inr _ _ _) = _ , sub-ren-m (λ {Hd → refl; (Tl x₂) → refl}) , match+-inr _ _ _