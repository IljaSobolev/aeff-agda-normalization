open import AEff
open import Renamings
open import Types hiding (``)

open import Finality
open import Substitutions
open import Renamings
open import Preservation using (strengthen-val)

open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_)

-- proof of the substitution lemma
-- almost all of the code and ideas from https://plfa.github.io/Substitution/

↑↑ : {Γ : Ctx} {X : Type} → Sub Γ (Γ ∷ X)
↑↑ x = ` (Tl x)

infixr 5 _⨟_

_⨟_ : {Γ Γ' Γ'' : Ctx} →
      Sub Γ Γ' →
      Sub Γ' Γ'' →
      -----------------
      Sub Γ Γ''
(s ⨟ s') x = (s x) [ s' ]v

infixr 6 _•_

_•_ : {Γ Γ' : Ctx} {X : Type} → (Γ' ⊢V⦂ X) → Sub Γ Γ' → Sub (Γ ∷ X) Γ'
(M • s) Hd = M
(M • s) (Tl x) = s x


sub-head : {Γ Γ' : Ctx} {X : Type} {V : Γ' ⊢V⦂ X} (s : Sub Γ Γ')
         → (` Hd) [ s [ V ]s ]v ≡ V
sub-head s = refl

sub-tail : {Γ Γ' : Ctx} {X Y : Type} {V : Γ' ⊢V⦂ X} {s : Sub Γ Γ'} (x : Y ∈ Γ)
         → (↑↑ ⨟ (s [ V ]s)) x ≡ s x
sub-tail x = refl

sub-η : {Γ Γ' : Ctx} {X Y : Type} {s : Sub (Γ ∷ X) Γ'} (x : Y ∈ Γ ∷ X)
      → ((↑↑ ⨟ s) [ (` Hd) [ s ]v ]s) x ≡ s x
sub-η Hd = refl
sub-η (Tl x) = refl

Z-shift : {Γ : Ctx} {X Y : Type} (x : Y ∈ Γ ∷ X)
        → (↑↑ [ ` Hd ]s) x ≡ id-subst x
Z-shift Hd = refl
Z-shift (Tl x) = refl

sub-idL : {Γ Γ' : Ctx} {s : Sub Γ Γ'} {X : Type} (x : X ∈ Γ)
       → (id-subst ⨟ s) x ≡ s x
sub-idL x = refl

sub-dist : {Γ Γ' Γ'' : Ctx} {X Y : Type}
           {s : Sub Γ Γ'} {t : Sub Γ' Γ''}
           {V : Γ' ⊢V⦂ X}
           (x : Y ∈ Γ ∷ X) →
           ((V • s) ⨟ t) x ≡ ((V [ t ]v) • (s ⨟ t)) x
sub-dist Hd = refl
sub-dist (Tl x) = refl

sub-app : {Γ Γ' : Ctx} {X Y : Type} {s : Sub Γ Γ'} {V : Γ ⊢V⦂ X ⇒ Y} {W : Γ ⊢V⦂ X}
        → (V · W) [ s ]m ≡ (V [ s ]v) · (W [ s ]v)
sub-app = refl

cong-wk₂ : {Γ Γ' : Ctx} {r r' : Ren Γ Γ'} {X : Type}
   → ({Y : Type} (x : Y ∈ Γ) → r x ≡ r' x)
     ---------------------------------
   → {Y : Type} (x : Y ∈ Γ ∷ X) → wk₂ r x ≡ wk₂ r' x
cong-wk₂ f Hd = refl
cong-wk₂ f (Tl x) = cong Tl (f x)

cong-lift : {Γ Γ' : Ctx} {s t : Sub Γ Γ'} {X : Type}
   → ({Y : Type} (x : Y ∈ Γ) → s {Y} x ≡ t {Y} x)
     -----------------------------------
   → {Y : Type} (x : Y ∈ Γ ∷ X) → lift s x ≡ lift t x
cong-lift f {Y} Hd = refl
cong-lift f {Y} (Tl x) = cong (V-rename Tl) (f x)

cong-sub-v : {Γ Γ' : Ctx}
             {X : Type}
             {s t : Sub Γ Γ'}
             {V : Γ ⊢V⦂ X} →
             ({Y : Type} (x : Y ∈ Γ) → s {Y} x ≡ t {Y} x) →
             V [ s ]v ≡ V [ t ]v

cong-sub-m : {Γ Γ' : Ctx}
             {X : Type}
             {s t : Sub Γ Γ'}
             {M : Γ ⊢M⦂ X} →
             ({Y : Type} (x : Y ∈ Γ) → s {Y} x ≡ t {Y} x) →
             M [ s ]m ≡ M [ t ]m

cong-sub-v {V = ` x} f = f x
cong-sub-v {V = `` c} f = refl
cong-sub-v {V = ƛ N} f = cong ƛ (cong-sub-m (λ x → cong-lift f x))
cong-sub-v {V = ⟨ V ⟩} f = cong ⟨_⟩ (cong-sub-v {V = V} f)
cong-sub-v {V = ★} f = refl

cong-sub-m {M = return V} f = cong return (cong-sub-v {V = V} f)
cong-sub-m {M = let= M `in N} f = cong₂ let=_`in_ (cong-sub-m f) (cong-sub-m (cong-lift f))
cong-sub-m {M = V · W} f = cong₂ _·_ (cong-sub-v {V = V} f) (cong-sub-v {V = W} f)
cong-sub-m {M = ↑ op V N} f = cong₂ (↑ op) (cong-sub-v {V = V} f) (cong-sub-m f)
cong-sub-m {M = ↓ op V N} f = cong₂ (↓ op) (cong-sub-v {V = V} f) (cong-sub-m f)
cong-sub-m {M = promise op ↦ M `in N} f = cong₂ (promise op ↦_`in_) (cong-sub-m (cong-lift f)) (cong-sub-m (cong-lift f))
cong-sub-m {M = await V until N} f = cong₂ await_until_ (cong-sub-v {V = V} f) (cong-sub-m (cong-lift f))

cong-cons : {Γ Γ' : Ctx} {X Y : Type} {s s' : Sub Γ Γ'} {V W : Γ' ⊢V⦂ X} →
            ({Z : Type} {x : Z ∈ Γ} → s x ≡ s' x) →
            V ≡ W →
            (x : Y ∈ Γ ∷ X) →
            --------------------------------
            (V • s) x ≡ (W • s') x
cong-cons eq refl Hd = refl
cong-cons eq refl (Tl x) = eq

cong-seq : {Γ Γ' Γ'' : Ctx} {Y : Type}
           {s s' : Sub Γ Γ'}
           {t t' : Sub Γ' Γ''} →
           ({Z : Type} {x : Z ∈ Γ} → s x ≡ s' x) →
           ({Z : Type} {x : Z ∈ Γ'} → t x ≡ t' x) →
           (x : Y ∈ Γ) →
           ----------------------------------------
           (s ⨟ t) x ≡ (s' ⨟ t') x
cong-seq {s = s} {s' = s'} {t = t} {t' = t'} ss' tt' x =
  begin
    (s ⨟ t) x
  ≡⟨ cong (_[ t ]v) ss' ⟩
    (s' x) [ t ]v
  ≡⟨ cong-sub-v {V = s' x} (λ _ → tt') ⟩
    (s' ⨟ t') x
  ∎

ren : {Γ Γ' : Ctx} → Ren Γ Γ' → Sub Γ Γ'
ren r x = ` (r x)

ren-wk₂ : {Γ Γ' : Ctx} {X Y : Type}
          {r : Ren Γ Γ'}
          (x : X ∈ Γ ∷ Y) →
          -------------------------------------
          ren (wk₂ {X = Y} r) x ≡ lift {X = Y} (ren r) x
ren-wk₂ Hd = refl
ren-wk₂ (Tl x) = refl

rename-subst-ren-v : {Γ Γ' : Ctx} {X : Type} {r : Ren Γ Γ'} {V : Γ ⊢V⦂ X}
                 → V-rename r V ≡ V [ ren r ]v
rename-subst-ren-m : {Γ Γ' : Ctx} {X : Type} {r : Ren Γ Γ'} {M : Γ ⊢M⦂ X}
                 → M-rename r M ≡ M [ ren r ]m

rename-subst-ren-v {V = ` x} = refl
rename-subst-ren-v {V = `` c} = refl
rename-subst-ren-v {r = r} {V = ƛ M} = cong ƛ (trans rename-subst-ren-m (cong-sub-m ren-wk₂))
rename-subst-ren-v {V = ⟨ V ⟩} = cong ⟨_⟩ rename-subst-ren-v
rename-subst-ren-v {V = ★} = refl

rename-subst-ren-m {M = return V} = cong return rename-subst-ren-v
rename-subst-ren-m {M = let= M `in N}
  = cong₂ let=_`in_ rename-subst-ren-m (trans rename-subst-ren-m (cong-sub-m ren-wk₂))
rename-subst-ren-m {M = V · W} = cong₂ _·_ rename-subst-ren-v rename-subst-ren-v
rename-subst-ren-m {M = ↑ op V M} = cong₂ (↑ op) rename-subst-ren-v rename-subst-ren-m
rename-subst-ren-m {M = ↓ op V M} = cong₂ (↓ op) rename-subst-ren-v rename-subst-ren-m
rename-subst-ren-m {M = promise op ↦ M `in N}
  = cong₂ (promise op ↦_`in_) (trans rename-subst-ren-m (cong-sub-m ren-wk₂)) (trans rename-subst-ren-m (cong-sub-m ren-wk₂))
rename-subst-ren-m {M = await V until M} = cong₂ await_until_ rename-subst-ren-v (trans rename-subst-ren-m (cong-sub-m ren-wk₂))

lift-cons-shift : {Γ Γ' : Ctx} {X Y : Type} {s : Sub Γ Γ'} (x : X ∈ Γ ∷ Y)
                → (lift s) x ≡ (` Hd • (s ⨟ ↑↑)) x
lift-cons-shift Hd = refl
lift-cons-shift (Tl x) = rename-subst-ren-v

wk₂-cons-Z-shift : {Γ Γ' : Ctx} {X Y : Type}
                   {r : Ren Γ Γ'}
                   (x : Y ∈ Γ ∷ X) →
                   ----------------------------------------
                   ren (wk₂ r) x ≡ (` Hd • (ren r ⨟ ↑↑)) x
wk₂-cons-Z-shift {r = r} x =
  begin
    ren (wk₂ r) x
  ≡⟨ ren-wk₂ x ⟩
    lift (ren r) x
  ≡⟨ lift-cons-shift {s = ren r} x ⟩
   ((` Hd) • (ren r ⨟ ↑↑)) x
  ∎

subst-Z-cons-ids : {Γ : Ctx} {X Y : Type}
                   {V : Γ ⊢V⦂ Y} →
                   (x : X ∈ Γ ∷ Y) →
                   ----------------------------
                   (id-subst [ V ]s) x ≡ (V • id-subst) x
subst-Z-cons-ids Hd = refl
subst-Z-cons-ids (Tl x) = refl
 
lift-ids : {Γ : Ctx} {X Y : Type} (x : X ∈ Γ ∷ Y)
         → (lift {X = Y} id-subst) x ≡ id-subst x
lift-ids Hd = refl
lift-ids (Tl x) = refl

sub-abs : {Γ Γ' : Ctx} {X Y : Type} {s : Sub Γ Γ'} {N : Γ ∷ X ⊢M⦂ Y}
        → (ƛ N) [ s ]v ≡ ƛ (N [ ` Hd • (s ⨟ ↑↑) ]m)
sub-abs {N = N} = cong ƛ (cong-sub-m lift-cons-shift)

sub-id-v : {Γ : Ctx} {X : Type} {V : Γ ⊢V⦂ X}
         → V [ id-subst ]v ≡ V
sub-id-m : {Γ : Ctx} {X : Type} {M : Γ ⊢M⦂ X}
         → M [ id-subst ]m ≡ M

ren-id-v : {Γ : Ctx} {X : Type} {V : Γ ⊢V⦂ X} → V-rename id-ren V ≡ V
ren-id-v {V = V} =
  begin
    V-rename id-ren V
  ≡⟨ rename-subst-ren-v ⟩
    V [ ren id-ren ]v
  ≡⟨ cong-sub-v {V = V} (λ x → refl) ⟩
    V [ id-subst ]v
  ≡⟨ sub-id-v ⟩
    V
  ∎

ren-id-m : {Γ : Ctx} {X : Type} {M : Γ ⊢M⦂ X} → M-rename id-ren M ≡ M
ren-id-m {M = M} =
  begin
    M-rename id-ren M
  ≡⟨ rename-subst-ren-m ⟩
    M [ ren id-ren ]m
  ≡⟨ cong-sub-m {M = M} (λ x → refl) ⟩
    M [ id-subst ]m
  ≡⟨ sub-id-m ⟩
    M
  ∎

sub-id-v {V = ` x} = refl
sub-id-v {V = `` c} = refl
sub-id-v {V = ƛ M} = cong ƛ (trans (cong-sub-m lift-ids) sub-id-m)
sub-id-v {V = ⟨ V ⟩} = cong ⟨_⟩ sub-id-v
sub-id-v {V = ★} = refl

sub-id-m {M = return V} = cong return sub-id-v
sub-id-m {M = let= M `in N} = cong₂ let=_`in_ sub-id-m (trans (cong-sub-m lift-ids) sub-id-m)
sub-id-m {M = V · W} = cong₂ _·_ sub-id-v sub-id-v
sub-id-m {M = ↑ op V M} = cong₂ (↑ op) sub-id-v sub-id-m
sub-id-m {M = ↓ op V M} = cong₂ (↓ op) sub-id-v sub-id-m
sub-id-m {M = promise op ↦ M `in N} = cong₂ (promise op ↦_`in_) (trans (cong-sub-m lift-ids) sub-id-m) (trans (cong-sub-m lift-ids) sub-id-m)
sub-id-m {M = await V until M} = cong₂ await_until_ sub-id-v (trans (cong-sub-m lift-ids) sub-id-m)

sub-idR : {Γ Γ' : Ctx} {s : Sub Γ Γ'} {X : Type} (x : X ∈ Γ)
       → (s ⨟ id-subst) x ≡ s x
sub-idR x = sub-id-v

compose-wk₂ : {Γ Γ' Γ'' : Ctx} {r : Ren Γ' Γ''} {r' : Ren Γ Γ'} {X Y : Type} (x : Y ∈ Γ ∷ X)
            → ((wk₂ r) ∘ (wk₂ r')) x ≡ wk₂ (r ∘ r') x
compose-wk₂ Hd = refl
compose-wk₂ (Tl x) = refl

cong-rename-v : {Γ Γ' : Ctx} {r r' : Ren Γ Γ'} {X : Type} {V : Γ ⊢V⦂ X}
        → ({Y : Type} (x : Y ∈ Γ) → r x ≡ r' x)
          ------------------------
        → V-rename r V ≡ V-rename r' V
cong-rename-m : {Γ Γ' : Ctx} {r r' : Ren Γ Γ'} {X : Type} {M : Γ ⊢M⦂ X}
        → ({Y : Type} (x : Y ∈ Γ) → r x ≡ r' x)
          ------------------------
        → M-rename r M ≡ M-rename r' M

cong-rename-v {V = ` x} f = cong `_ (f x)
cong-rename-v {V = `` c} f = refl
cong-rename-v {V = ƛ M} f = cong ƛ (cong-rename-m (cong-wk₂ f))
cong-rename-v {V = ⟨ V ⟩} f = cong ⟨_⟩ (cong-rename-v f)
cong-rename-v {V = ★} f = refl

cong-rename-m {M = return V} f = cong return (cong-rename-v f)
cong-rename-m {M = let= M `in N} f = cong₂ let=_`in_ (cong-rename-m f) (cong-rename-m (cong-wk₂ f))
cong-rename-m {M = V · W} f = cong₂ _·_ (cong-rename-v f) (cong-rename-v f)
cong-rename-m {M = ↑ op V M} f = cong₂ (↑ op) (cong-rename-v f) (cong-rename-m f)
cong-rename-m {M = ↓ op V M} f = cong₂ (↓ op) (cong-rename-v f) (cong-rename-m f)
cong-rename-m {M = promise op ↦ M `in N} f = cong₂ (promise op ↦_`in_) (cong-rename-m (cong-wk₂ f)) (cong-rename-m (cong-wk₂ f))
cong-rename-m {M = await V until M} f = cong₂ await_until_ (cong-rename-v f) (cong-rename-m (cong-wk₂ f))

compose-rename-v : {Γ Γ' Γ'' : Ctx} {X : Type} {V : Γ ⊢V⦂ X} {r : Ren Γ' Γ''} {r' : Ren Γ Γ'}
  → V-rename r (V-rename r' V) ≡ V-rename (r ∘ r') V
compose-rename-m : {Γ Γ' Γ'' : Ctx} {X : Type} {M : Γ ⊢M⦂ X} {r : Ren Γ' Γ''} {r' : Ren Γ Γ'}
  → M-rename r (M-rename r' M) ≡ M-rename (r ∘ r') M

compose-rename-v {V = ` x} = refl
compose-rename-v {V = `` c} = refl
compose-rename-v {V = ƛ M} = cong ƛ (trans compose-rename-m (cong-rename-m compose-wk₂))
compose-rename-v {V = ⟨ V ⟩} = cong ⟨_⟩ compose-rename-v
compose-rename-v {V = ★} = refl

compose-rename-m {M = return V} = cong return compose-rename-v
compose-rename-m {M = let= M `in N} = cong₂ let=_`in_ compose-rename-m (trans compose-rename-m (cong-rename-m compose-wk₂))
compose-rename-m {M = V · W} = cong₂ _·_ compose-rename-v compose-rename-v
compose-rename-m {M = ↑ op V M} = cong₂ (↑ op) compose-rename-v compose-rename-m
compose-rename-m {M = ↓ op V M} = cong₂ (↓ op) compose-rename-v compose-rename-m
compose-rename-m {M = promise op ↦ M `in N} = cong₂ (promise op ↦_`in_) (trans compose-rename-m (cong-rename-m compose-wk₂)) (trans compose-rename-m (cong-rename-m compose-wk₂))
compose-rename-m {M = await V until M} = cong₂ await_until_ compose-rename-v (trans compose-rename-m (cong-rename-m compose-wk₂))

-- since this is a typed calculus, the proof of the
-- commute-subst-rename functions from PLFA does not work,
-- instead we prove the following generalizations:

commute-subst-rename-v :  {Γ Γ' Δ Δ' : Ctx} {X : Type} {V : Γ ⊢V⦂ X}
                          {s : Sub Γ Δ} {s' : Sub Γ' Δ'}
                          {rΓ : Ren Γ Γ'} {rΔ : Ren Δ Δ'} →
                          ({C : Type} (x : C ∈ Γ) → s' (rΓ x) ≡ V-rename rΔ (s x)) →
                          (V-rename rΓ V) [ s' ]v ≡ V-rename rΔ (V [ s ]v)
commute-subst-rename-m :  {Γ Γ' Δ Δ' : Ctx} {X : Type} {M : Γ ⊢M⦂ X}
                          {s : Sub Γ Δ} {s' : Sub Γ' Δ'}
                          {rΓ : Ren Γ Γ'} {rΔ : Ren Δ Δ'} →
                          ({C : Type} (x : C ∈ Γ) → s' (rΓ x) ≡ V-rename rΔ (s x)) →
                          (M-rename rΓ M) [ s' ]m ≡ M-rename rΔ (M [ s ]m)

commute-subst-rename-lift : {Γ Γ' Δ Δ' : Ctx} {X Y : Type} {M : (Γ ∷ X) ⊢M⦂ Y}
                            {s : Sub Γ Δ } {s' : Sub Γ' Δ'}
                            {rΓ : Ren Γ Γ'} {rΔ : Ren Δ Δ'} →
                            ({C : Type} (x : C ∈ Γ) → s' (rΓ x) ≡ V-rename rΔ (s x)) →
                            M-rename (wk₂ rΓ) M [ lift s' ]m ≡ M-rename (wk₂ rΔ) (M [ lift s ]m)
commute-subst-rename-lift {Γ} {X = X} {M = M} {s} {s'} {rΓ} {rΔ} H
  = commute-subst-rename-m {M = M} {lift s} {lift s'} {wk₂ rΓ} {wk₂ rΔ} (λ {Z} → H')
  where
  H' : {Z : Type} (x : Z ∈ Γ ∷ X) → lift s' (wk₂ rΓ x) ≡ V-rename (wk₂ rΔ) (lift s x)
  H' Hd = refl
  H' (Tl x) =
    begin
      V-rename wk₁ (s' (rΓ x))
    ≡⟨ cong (V-rename wk₁) (H x) ⟩
      V-rename Tl (V-rename rΔ (s x))
    ≡⟨ compose-rename-v ⟩
      V-rename (wk₁ ∘ rΔ) (s x)
    ≡⟨ sym compose-rename-v ⟩
      V-rename (wk₂ rΔ) ((lift s) (Tl x))
    ∎

commute-subst-rename-v {V = ` x} H = H x
commute-subst-rename-v {V = `` c} H = refl
commute-subst-rename-v {V = ƛ M} H = cong ƛ (commute-subst-rename-lift H)
commute-subst-rename-v {V = ⟨ V ⟩} H = cong ⟨_⟩ (commute-subst-rename-v {V = V} H)
commute-subst-rename-v {V = ★} H = refl

commute-subst-rename-m {M = return V} H = cong return (commute-subst-rename-v {V = V} H)
commute-subst-rename-m {M = let= M `in N} H = cong₂ let=_`in_ (commute-subst-rename-m H) (commute-subst-rename-lift H)
commute-subst-rename-m {M = V · W} H = cong₂ _·_ (commute-subst-rename-v {V = V} H) (commute-subst-rename-v {V = W} H)
commute-subst-rename-m {M = ↑ op V M} H = cong₂ (↑ op) (commute-subst-rename-v {V = V} H) (commute-subst-rename-m H)
commute-subst-rename-m {M = ↓ op V M} H = cong₂ (↓ op) (commute-subst-rename-v {V = V} H) (commute-subst-rename-m H)
commute-subst-rename-m {M = promise op ↦ M `in N} H = cong₂ (promise op ↦_`in_) (commute-subst-rename-lift H) (commute-subst-rename-lift H)
commute-subst-rename-m {M = await V until M} H = cong₂ await_until_ (commute-subst-rename-v {V = V} H) (commute-subst-rename-lift H)

lift-seq : {Γ Γ' Γ'' : Ctx} {X Y : Type} {s : Sub Γ Γ'} {s' : Sub Γ' Γ''} (x : Y ∈ (Γ ∷ X))
  → (lift s ⨟ lift s') x ≡ lift (s ⨟ s') x
lift-seq Hd = refl
lift-seq {s = s} {s' = s'} (Tl x) = commute-subst-rename-v {V = s x} (λ z → refl)

sub-sub-v : {Γ Γ' Γ'' : Ctx} {X : Type} {s : Sub Γ Γ'} {s' : Sub Γ' Γ''} (V : Γ ⊢V⦂ X)
            → (V [ s ]v) [ s' ]v ≡ V [ s ⨟ s' ]v
sub-sub-m : {Γ Γ' Γ'' : Ctx} {X : Type} {s : Sub Γ Γ'} {s' : Sub Γ' Γ''} (M : Γ ⊢M⦂ X)
            → (M [ s ]m) [ s' ]m ≡ M [ s ⨟ s' ]m

sub-sub-lift : {Γ Γ' Γ'' : Ctx} {X C : Type}
               {s : Sub Γ Γ'} {s' : Sub Γ' Γ''}
               (N : (Γ ∷ X) ⊢M⦂ C) →
               (N [ lift s ]m) [ lift s' ]m ≡ N [ lift (s ⨟ s') ]m
sub-sub-lift {s = s} {s' = s'} N =
  begin
    (N [ lift s ]m) [ lift s' ]m
  ≡⟨ sub-sub-m N ⟩
    N [ lift s ⨟ lift s' ]m
  ≡⟨ cong-sub-m lift-seq ⟩
    N [ lift (s ⨟ s') ]m
  ∎

sub-sub-v (` x) = refl
sub-sub-v (`` c) = refl
sub-sub-v (ƛ N) = cong ƛ (sub-sub-lift N)
sub-sub-v ⟨ V ⟩ = cong ⟨_⟩ (sub-sub-v V)
sub-sub-v ★ = refl

sub-sub-m (return V) = cong return (sub-sub-v V)
sub-sub-m (let= M `in N) = cong₂ let=_`in_ (sub-sub-m M) (sub-sub-lift N)
sub-sub-m (V · W) = cong₂ _·_ (sub-sub-v V) (sub-sub-v W)
sub-sub-m (↑ op V M) = cong₂ (↑ op) (sub-sub-v V) (sub-sub-m M)
sub-sub-m (↓ op V M) = cong₂ (↓ op) (sub-sub-v V) (sub-sub-m M)
sub-sub-m (promise op ↦ M `in N) = cong₂ (promise op ↦_`in_) (sub-sub-lift M) (sub-sub-lift N)
sub-sub-m (await V until M) = cong₂ await_until_ (sub-sub-v V) (sub-sub-lift M)

ren-ren-v : {Γ Γ' Γ'' : Ctx} {X : Type} {rn : Ren Γ Γ'} {rn' : Ren Γ' Γ''} (V : Γ ⊢V⦂ X)
            → V-rename rn' (V-rename rn V) ≡ V-rename (rn' ∘ rn) V
ren-ren-m : {Γ Γ' Γ'' : Ctx} {X : Type} {rn : Ren Γ Γ'} {rn' : Ren Γ' Γ''} (M : Γ ⊢M⦂ X)
            → M-rename rn' (M-rename rn M) ≡ M-rename (rn' ∘ rn) M
ren-ren-v {rn = rn} {rn' = rn'} V
  rewrite rename-subst-ren-v {r = rn} {V = V}
  | rename-subst-ren-v {r = rn'} {V = V [ ren rn ]v}
  | rename-subst-ren-v {r = rn' ∘ rn} {V = V}
  = sub-sub-v V
ren-ren-m {rn = rn} {rn' = rn'} M
  rewrite rename-subst-ren-m {r = rn} {M = M}
  | rename-subst-ren-m {r = rn'} {M = M [ ren rn ]m}
  | rename-subst-ren-m {r = rn' ∘ rn} {M = M}
  = sub-sub-m M

sub-assoc : {Γ Γ' Γ'' Γ''' : Ctx} {X : Type}
            {s : Sub Γ Γ'} {s' : Sub Γ' Γ''} {s'' : Sub Γ'' Γ'''}
            (x : X ∈ Γ) →
            ((s ⨟ s') ⨟ s'') x ≡ (s ⨟ (s' ⨟ s'')) x
sub-assoc {s = s} {s' = s'} {s'' = s''} x = sub-sub-v (s x)

subst-zero-lift-cons : {Γ Γ' : Ctx} {X Y : Type}
                       {s : Sub Γ Γ'} {V : Γ' ⊢V⦂ Y}
                       (x : X ∈ Γ ∷ Y) →
                       (lift s ⨟ (id-subst [ V ]s)) x ≡ (V • s) x
subst-zero-lift-cons {Γ} {Γ'} {X} {Y} {s} {V} x =
  begin
    (lift s ⨟ (id-subst [ V ]s)) x
  ≡⟨ cong-seq (λ {_} {y} → lift-cons-shift y) (λ {_} {y} → subst-Z-cons-ids {V = V} y) x ⟩
    (((` Hd) • (s ⨟ ↑↑)) ⨟ (V • id-subst)) x
  ≡⟨ sub-dist x ⟩
    (((` Hd) [ V • id-subst ]v) • ((s ⨟ ↑↑) ⨟ (V • id-subst))) x
  ≡⟨ cong-cons (sub-head id-subst) refl x ⟩
    (V • ((s ⨟ ↑↑) ⨟ (V • id-subst))) x
  ≡⟨ cong-cons (λ {_} {y} → sub-assoc {s = s} y) refl x ⟩
    (V • (s ⨟ (↑↑ ⨟ (V • id-subst)))) x
  ≡⟨ cong-cons (λ {_} {y} → cong-seq {s = s} refl (λ {_} {z} → sub-tail {V = V} {s = id-subst} z) y) refl x ⟩
    (V • (s ⨟ id-subst)) x
  ≡⟨ cong-cons (λ {_} {y} → sub-idR {s = s} y) refl x ⟩
    (V • s) x
  ∎ 

substitution-lemma-v : {Γ Γ' : Ctx} {X Y : Type}
                       {s : Sub Γ Γ'}
                       {V : Γ ∷ X ⊢V⦂ Y} {W : Γ ⊢V⦂ X} →
                       -------------------------
                       V [ lift s ]v [ id-subst [ W [ s ]v ]s ]v ≡ (V [ id-subst [ W ]s ]v) [ s ]v
substitution-lemma-v {Γ} {Γ'} {X} {Y} {s} {V} {W} =
  begin
    V [ lift s ]v [ id-subst [ W [ s ]v ]s ]v
  ≡⟨ cong-sub-v {V = V [ lift s ]v} (subst-Z-cons-ids) ⟩
    (V [ lift s ]v) [ (W [ s ]v) • id-subst ]v
  ≡⟨ sub-sub-v V ⟩
    V [ (lift s) ⨟ ((W [ s ]v) • id-subst) ]v
  ≡⟨ cong-sub-v {V = V} (cong-seq (λ {_} {y} → lift-cons-shift y) refl) ⟩
    V [ (` Hd • (s ⨟ ↑↑)) ⨟ ((W [ s ]v) • id-subst) ]v
  ≡⟨ cong-sub-v {V = V} sub-dist ⟩
    V [ (` Hd) [ (W [ s ]v) • id-subst ]v • ((s ⨟ ↑↑) ⨟ ((W [ s ]v) • id-subst)) ]v
  ≡⟨ cong-sub-v {V = V} (cong-cons (λ {_} {y} → sub-assoc {s = s} y) refl) ⟩
    V [ (W [ s ]v) • (s ⨟ (↑↑ ⨟ ((W [ s ]v) • id-subst))) ]v
  ≡⟨ cong-sub-v {V = V} (λ {_} x → refl) ⟩
    V [ W [ s ]v • (s ⨟ id-subst) ]v
  ≡⟨ cong-sub-v {V = V} (cong-cons (λ {_} {y} → sub-idR {s = s} y) refl) ⟩
    V [ W [ s ]v • s ]v
  ≡⟨ cong-sub-v {V = V} (cong-cons (λ {_} {y} → sub-idL {s = s} y) refl) ⟩
    V [ W [ s ]v • (id-subst ⨟ s) ]v
  ≡⟨ cong-sub-v {V = V} (λ x → sym (sub-dist x)) ⟩
    V [ (W • id-subst) ⨟ s ]v
  ≡⟨ sym (sub-sub-v V) ⟩
    (V [ W • id-subst ]v) [ s ]v
  ≡⟨ cong (_[ s ]v) (sym (cong-sub-v {V = V} subst-Z-cons-ids)) ⟩
    (V [ id-subst [ W ]s ]v) [ s ]v
  ∎

substitution-lemma-m : {Γ Γ' : Ctx} {X Y : Type}
                       {s : Sub Γ Γ'}
                       {N : Γ ∷ X ⊢M⦂ Y} {V : Γ ⊢V⦂ X} →
                       -------------------------
                       N [ lift s ]m [ id-subst [ V [ s ]v ]s ]m ≡ (N [ id-subst [ V ]s ]m) [ s ]m
substitution-lemma-m {Γ} {Γ'} {X} {Y} {s} {N} {V} =
  begin
    N [ lift s ]m [ id-subst [ V [ s ]v ]s ]m
  ≡⟨ cong-sub-m {M = N [ lift s ]m} (subst-Z-cons-ids) ⟩
    (N [ lift s ]m) [ (V [ s ]v) • id-subst ]m
  ≡⟨ sub-sub-m N ⟩
    N [ (lift s) ⨟ ((V [ s ]v) • id-subst) ]m
  ≡⟨ cong-sub-m {M = N} (cong-seq (λ {_} {y} → lift-cons-shift y) refl) ⟩
    N [ (` Hd • (s ⨟ ↑↑)) ⨟ ((V [ s ]v) • id-subst) ]m
  ≡⟨ cong-sub-m {M = N} sub-dist ⟩
    N [ (` Hd) [ (V [ s ]v) • id-subst ]v • ((s ⨟ ↑↑) ⨟ ((V [ s ]v) • id-subst)) ]m
  ≡⟨ cong-sub-m {M = N} (cong-cons (λ {_} {y} → sub-assoc {s = s} y) refl) ⟩
    N [ (V [ s ]v) • (s ⨟ (↑↑ ⨟ ((V [ s ]v) • id-subst))) ]m
  ≡⟨ cong-sub-m {M = N} (λ {_} x → refl) ⟩
    N [ V [ s ]v • (s ⨟ id-subst) ]m
  ≡⟨ cong-sub-m {M = N} (cong-cons (λ {_} {y} → sub-idR {s = s} y) refl) ⟩
    N [ V [ s ]v • s ]m
  ≡⟨ cong-sub-m {M = N} (cong-cons (λ {_} {y} → sub-idL {s = s} y) refl) ⟩
    N [ V [ s ]v • (id-subst ⨟ s) ]m
  ≡⟨ cong-sub-m {M = N} (λ x → sym (sub-dist x)) ⟩
    N [ (V • id-subst) ⨟ s ]m
  ≡⟨ sym (sub-sub-m N) ⟩
    (N [ V • id-subst ]m) [ s ]m
  ≡⟨ cong (_[ s ]m) (sym (cong-sub-m {M = N} subst-Z-cons-ids)) ⟩
    (N [ id-subst [ V ]s ]m) [ s ]m
  ∎

strengthen-lemma : {Γ Γ' : Ctx}
                   {X : Type}
                   {c : BType}
                   (s : Sub Γ Γ')
                   (V : ((Γ ∷ ⟨ X ⟩) ⊢V⦂ Type.`` c)) →
                   -------------------------------------------
                   (strengthen-val {Δ = X ∷ₗ []} V) [ s ]v ≡ strengthen-val {Δ = X ∷ₗ []} (V [ lift {X = ⟨ X ⟩} s ]v)
strengthen-lemma s (` Tl x) with s x
... | ` y = refl
... | `` c = refl
strengthen-lemma s (`` c) = refl

-- finally, the result that substitution preserves reductions

sub-↝↝ : {Γ Γ' : Ctx} {X : Type}
         {M N : Γ ⊢M⦂ X}
         (s : Sub Γ Γ') →
         M ↝↝ N →
         ----------------------
         M [ s ]m ↝↝ N [ s ]m
sub-↝↝ s (apply M V) rewrite sym (substitution-lemma-m {s = s} {N = M} {V = V}) = apply (M [ lift s ]m) (V [ s ]v)
sub-↝↝ s (let-return V N) rewrite sym (substitution-lemma-m {s = s} {N = N} {V = V}) = let-return (V [ s ]v) (N [ lift s ]m)
sub-↝↝ s (let-↑ V M N) = let-↑ (V [ s ]v) (M [ s ]m) (N [ lift s ]m)
sub-↝↝ s (let-promise {X} M₁ M₂ N)
  rewrite commute-subst-rename-m {M = N} {s' = lift (lift {X = ⟨ X ⟩} s)} {rΓ = comp-ren exchange wk₁}
          (λ {Hd → refl
           ; (Tl x) → trans compose-rename-v (trans refl (sym compose-rename-v))})
  = let-promise (M₁ [ lift s ]m) (M₂ [ lift s ]m) (N [ lift s ]m)
sub-↝↝ s (promise-↑ V M N) rewrite strengthen-lemma s V = promise-↑ (V [ lift s ]v) (M [ lift s ]m) (N [ lift s ]m)
sub-↝↝ s (↓-return V W) = ↓-return (V [ s ]v) (W [ s ]v)
sub-↝↝ s (↓-↑ V W M) = ↓-↑ (V [ s ]v) (W [ s ]v) (M [ s ]m)
sub-↝↝ s (↓-promise-op {X} V M N)
  rewrite sym (substitution-lemma-m {s = s} {N = M} {V = V})
  | commute-subst-rename-v {V = V} {s = s} {s' = lift {X = ⟨ X ⟩} s} {rΓ = wk₁} {rΔ = wk₁} (λ x → refl)
  | sym (substitution-lemma-m {s = lift s} {N = M-rename (comp-ren exchange wk₁) N} {V = ` Hd})
  | commute-subst-rename-m {M = N} {s = lift s} {s' = lift (lift {X = ⟨ X ⟩} s)} {rΓ = comp-ren exchange wk₁} {rΔ = comp-ren exchange wk₁}
    (λ {Hd → refl
     ; (Tl x) → trans compose-rename-v (trans refl (sym compose-rename-v))})
  = ↓-promise-op (V [ s ]v) (M [ lift s ]m) (N [ lift s ]m)
sub-↝↝ s (↓-promise-op' {X} p V M N)
  rewrite commute-subst-rename-v {V = V} {s = s} {s' = lift {X = ⟨ X ⟩} s} {rΓ = wk₁} {rΔ = wk₁} (λ x → refl)
  = ↓-promise-op' p (V [ s ]v) (M [ lift s ]m) (N [ lift s ]m)
sub-↝↝ s (await-promise V M) rewrite sym (substitution-lemma-m {s = s} {N = M} {V = V}) = await-promise (V [ s ]v) (M [ lift s ]m)
sub-↝↝ s (context-let r) = context-let (sub-↝↝ s r)
sub-↝↝ s (context-↑ r) = context-↑ (sub-↝↝ s r)
sub-↝↝ s (context-↓ r) = context-↓ (sub-↝↝ s r) 
sub-↝↝ s (context-promise r) = context-promise (sub-↝↝ (lift s) r)

-- as a corollary, renaming preserves reductions

ren-↝↝ : {Γ Γ' : Ctx} {X : Type}
         {M N : Γ ⊢M⦂ X}
         (rn : Ren Γ Γ') →
         M ↝↝ N →
         ----------------------
         M-rename rn M ↝↝ M-rename rn N
ren-↝↝ {M = M} {N = N} rn r
  rewrite rename-subst-ren-m {r = rn} {M = M}
  | rename-subst-ren-m {r = rn} {M = N}
  = sub-↝↝ (λ x → ` rn x) r