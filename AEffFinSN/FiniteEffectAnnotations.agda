open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-trans; n≤1+n; m≤n⇒m<n∨m≡n)
open import Data.List using (List) renaming ([] to []ₗ; _∷_ to _∷ₗ_; [_] to [_]ₗ)

open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; sym; _≢_)

open import Function using (_∘_)

open import EffectAnnotations using (Σₛ; decₛ)

module AEffFinSN.FiniteEffectAnnotations where

private variable
  A B : Set
  x y : A

variable
  op op' : Σₛ

if_≡_then_else_ : Σₛ → Σₛ → A → A → A
if op ≡ op' then x else y with decₛ op op'
... | yes p = x
... | no ¬p = y

ite-≡ : if op ≡ op then x else y ≡ x
ite-≡ {op} with decₛ op op
... | yes p = refl
... | no ¬p = ⊥-elim (¬p refl)

ite-≢ : op ≢ op' → if op ≡ op' then x else y ≡ y
ite-≢ {op} {op'} p with decₛ op op'
... | yes q = ⊥-elim (p q)
... | no ¬q = refl


-- FINITE SETS OF PATHS AND THEIR PROPERTIES

Path : Set
Path = List Σₛ

variable
  p p' q q' : Path

infix 4 _≟_
_≟_ : (p q : Path) → Dec (p ≡ q)
[]ₗ ≟ []ₗ = yes refl
[]ₗ ≟ _ ∷ₗ _ = no (λ ())
_ ∷ₗ _ ≟ []ₗ = no (λ ())
op ∷ₗ ps ≟ op' ∷ₗ ps' with decₛ op op' | ps ≟ ps'
... | no     a |        _ = no (λ {refl → a refl})
... |        _ | no     a = no (λ {refl → a refl})
... | yes refl | yes refl = yes refl

data Paths : Set

_#_ : Path → Paths → Set

data Paths where
  []   : Paths
  cons : (p : Path) (ps : Paths) → p # ps → Paths

infix 4 _#_
p # [] = ⊤
p # cons p' ps _ = p ≢ p' × p # ps

variable
  ps ps' ps'' : Paths

_#?_ : (p : Path) (ps : Paths) → Dec (p # ps)
p #? [] = yes tt
p #? cons p' ps _ with p ≟ p'
... | yes a = no (λ (q , _) → q a)
... | no  a with p #? ps
...   | yes b = yes (a , b)
...   | no  b = no (λ (_ , p) → b p)

infix 4 _∈ₚ_
data _∈ₚ_ : Path → Paths → Set where
  Hd : {x : p # ps} → p ∈ₚ cons p ps x
  Tl : {x : p' # ps} → p ∈ₚ ps → p ∈ₚ cons p' ps x

len : Paths → ℕ
len [] = 0
len (cons _ ps _) = suc (len ps)

_↓_ : Σₛ → Path → Path
op ↓ []ₗ = []ₗ
op ↓ (op' ∷ₗ p) with decₛ op op'
... | yes _ = p
... | no  _ = op' ∷ₗ p

_↓↓_ : Path → Path → Path
[]ₗ ↓↓ p' = p'
(op ∷ₗ p) ↓↓ p' = op ↓ (p ↓↓ p')

map : (Path → Path) → Paths → Paths
map f [] = []
map f (cons p ps _) with f p #? map f ps
... | yes a = cons (f p) (map f ps) a
... | no  _ = map f ps

_↓ₚ_ : Σₛ → Paths → Paths
op ↓ₚ ps = map (op ↓_) ps

_↓↓ₚ_ : Path → Paths → Paths
op ↓↓ₚ ps = map (op ↓↓_) ps

¬∈-# : ¬ p ∈ₚ ps → p # ps
¬∈-# {ps = []} u = tt
¬∈-# {ps = cons _ _ _} u = (λ {refl → u Hd}) , ¬∈-# (u ∘ Tl)

#-¬∈ : p # ps → ¬ p ∈ₚ ps
#-¬∈ (u , _) Hd = u refl
#-¬∈ (_ , u) (Tl h) = #-¬∈ u h

¬#-∈ : ¬ p # ps → p ∈ₚ ps
¬#-∈ {p} {[]} u = ⊥-elim (u tt)
¬#-∈ {p} {cons p' ps _} u with p ≟ p'
... | yes refl = Hd
... | no     a with p #? ps
...   | yes b = ⊥-elim (u (a , b))
...   | no  b = Tl (¬#-∈ b)

↓-≡ : op ↓ (op ∷ₗ p) ≡ p
↓-≡ {op} {p} with decₛ op op
... | yes refl = refl
... | no     a = ⊥-elim (a refl)

startswith : Σₛ → Path → Set
startswith op []ₗ = ⊥
startswith op (op' ∷ₗ _) = op ≡ op'

↓-≢' : ¬ startswith op p → p ≡ op ↓ p
↓-≢' {op} {[]ₗ} u = refl
↓-≢' {op} {op' ∷ₗ _} u with decₛ op op'
... | yes a = ⊥-elim (u a)
... | no  _ = refl

∈-map-e : (f : Path → Path) (ps : Paths) → p ∈ₚ map f ps → Σ[ p' ∈ Path ] p' ∈ₚ ps × p ≡ f p'
∈-map-e f (cons p ps _) u with f p #? map f ps
... | no  _ with _ , u , h ← ∈-map-e f ps u = _ , Tl u , h
... | yes _ with u
...   | Hd = _ , Hd , refl
...   | Tl u with _ , u , h ← ∈-map-e f ps u = _ , Tl u , h

∈-map-i : (f : Path → Path) → p ∈ₚ ps → f p ∈ₚ map f ps
∈-map-i {ps = cons p ps _} f Hd with f p #? map f ps
... | yes _ = Hd
... | no  a = ¬#-∈ a
∈-map-i {ps = cons p ps _} f (Tl u) with f p #? map f ps
... | yes _ = Tl (∈-map-i f u)
... | no  _ = ∈-map-i f u

_⧵_ : Paths → Path → Paths

#-⧵-i : (ps : Paths) → p # ps → p # ps ⧵ p'

[] ⧵ p' = []
cons p ps x ⧵ p' with p' ≟ p
... | yes _ = ps
... | no  _ = cons p (ps ⧵ p') (#-⧵-i _ x)

#-⧵-i [] _ = tt
#-⧵-i {p' = p'} (cons p _ _) u with p' ≟ p
... | yes _ with _ , u ← u = u
... | no  _ with u , v ← u = u , #-⧵-i _ v

∈-⧵-i : p ∈ₚ ps → p ≢ p' → p ∈ₚ ps ⧵ p'
∈-⧵-i {ps = cons p _ _} {p'} Hd v with p' ≟ p
... | yes a = ⊥-elim (v (sym a))
... | no  _ = Hd
∈-⧵-i {ps = cons p _ _} {p'} (Tl u) v with p' ≟ p
... | yes refl = u
... | no  _ = Tl (∈-⧵-i u v)

lkpₚ : Σₛ → Paths → Paths

∈-lkp-e : (ps : Paths) → p ∈ₚ lkpₚ op ps → op ∷ₗ p ∈ₚ ps

lkpₚ op [] = []
lkpₚ op (cons []ₗ ps x) = lkpₚ op ps
lkpₚ op (cons (op' ∷ₗ p) ps x) with decₛ op op'
... | yes refl = cons p (lkpₚ op ps) (¬∈-# (λ h → #-¬∈ x (∈-lkp-e ps h)))
... | no     _ = lkpₚ op ps

∈-lkp-e (cons []ₗ ps x) u = Tl (∈-lkp-e ps u)
∈-lkp-e {op = op} (cons (op' ∷ₗ p) ps x) u with decₛ op op'
... | no     _ = Tl (∈-lkp-e ps u)
... | yes refl with u
...   | Hd = Hd
...   | Tl u = Tl (∈-lkp-e ps u)

∈-lkp-i : (ps : Paths) → op ∷ₗ p ∈ₚ ps → p ∈ₚ lkpₚ op ps
∈-lkp-i {op} (cons p ps x) Hd with decₛ op op
... | yes refl = Hd
... | no     a = ⊥-elim (a refl)
∈-lkp-i {op} (cons []ₗ ps x) (Tl u) = ∈-lkp-i ps u
∈-lkp-i {op} (cons (op' ∷ₗ p) ps x) (Tl u) with decₛ op op'
... | yes refl = Tl (∈-lkp-i ps u)
... | no     a = ∈-lkp-i ps u

len-⧵-≤ : (ps : Paths) → len (ps ⧵ p) ≤ len ps
len-⧵-≤ [] = z≤n
len-⧵-≤ {p'} (cons p ps _) with p' ≟ p
... | yes _ = n≤1+n _
... | no  _ = s≤s (len-⧵-≤ ps)

len-⧵-< : p ∈ₚ ps → len (ps ⧵ p) < len ps
len-⧵-< {p} {cons _ ps _} Hd with p ≟ p
... | yes _ = ≤-refl
... | no  a = ⊥-elim (a refl)
len-⧵-< {p} {cons p' ps _} (Tl u) with p ≟ p'
... | yes _ = ≤-refl
... | no  _ = s≤s (len-⧵-< u)

len-map-≤ : (f : Path → Path) (ps : Paths) → len (map f ps) ≤ len ps
len-map-≤ f [] = z≤n
len-map-≤ f (cons p ps _) with f p #? map f ps
... | yes _ = s≤s (len-map-≤ _ ps)
... | no  _ = ≤-trans (len-map-≤ _ ps) (n≤1+n _)

infix 4 _⊑ₚ_
_⊑ₚ_ : Paths → Paths → Set
ps ⊑ₚ ps' = {p : Path} → p ∈ₚ ps → p ∈ₚ ps'

cons-⧵ : cons p ps x ⊑ₚ ps' → ps ⊑ₚ ps' ⧵ p
cons-⧵ {p} {ps} {x} u {p'} v with p ≟ p'
... | yes refl = ⊥-elim (#-¬∈ x v)
... | no     a = ∈-⧵-i (u (Tl v)) (a ∘ sym)

len-⊑ : ps ⊑ₚ ps' → len ps ≤ len ps'
len-⊑ {[]} u = z≤n
len-⊑ {cons _ _ _} u = ≤-trans (s≤s (len-⊑ (cons-⧵ u))) (len-⧵-< (u Hd))

↓ₚ-⧵ : []ₗ ∈ₚ ps → op ↓ₚ ps ⊑ₚ op ↓ₚ (ps ⧵ [ op ]ₗ)
↓ₚ-⧵ {ps} {op} h v with ∈-map-e _ ps v
... | p , u , refl with p ≟ [ op ]ₗ
...   | yes refl rewrite ↓-≡ {op} {[]ₗ} = ∈-map-i _ (∈-⧵-i h (λ ()))
...   | no     a = ∈-map-i _ (∈-⧵-i u a)

len-↓ₚ-< : []ₗ ∈ₚ ps → [ op ]ₗ ∈ₚ ps → len (op ↓ₚ ps) < len ps
len-↓ₚ-< {ps} {op} u v = ≤-trans (s≤s (≤-trans (len-⊑ (↓ₚ-⧵ {ps} {op} u)) (len-map-≤ _ (ps ⧵ _)))) (len-⧵-< v)

⊑ₚ-↓ₚ : ({p : Path} → p ∈ₚ ps → ¬ startswith op p) → ps ⊑ₚ op ↓ₚ ps
⊑ₚ-↓ₚ u v rewrite ↓-≢' (u v) = ∈-map-i _ v

len-↓ₚ-≡ : ({p : Path} → p ∈ₚ ps → ¬ startswith op p) → len (op ↓ₚ ps) ≡ len ps
len-↓ₚ-≡ f = ≤-antisym (len-map-≤ _ _) (len-⊑ (⊑ₚ-↓ₚ f))


-- EFFECT ANNOTATIONS FOR INTERRUPT HANDLERS

data I : Set where
  leaf : I
  node : (Σₛ → I) → I

variable
  i i' i'' i''' : I
  f g : Σₛ → I

infix 10 _⊑_
data _⊑_ : I → I → Set where
  l⊑n : leaf ⊑ i
  n⊑n : ((op : Σₛ) → f op ⊑ g op) → node f ⊑ node g

⊑-refl : i ⊑ i
⊑-refl {leaf} = l⊑n
⊑-refl {node _} = n⊑n (λ _ → ⊑-refl)

⊑-trans : i ⊑ i' → i' ⊑ i'' → i ⊑ i''
⊑-trans l⊑n q = l⊑n
⊑-trans (n⊑n f) (n⊑n f') = n⊑n (λ op → ⊑-trans (f op) (f' op))

infix 15 _∪_
_∪_ : I → I → I
leaf ∪ i = i
node f ∪ leaf = node f
node f ∪ node g = node (λ op → f op ∪ g op)

∪-inl : i ⊑ i ∪ i'
∪-inl {leaf} {_} = l⊑n
∪-inl {node _} {leaf} = ⊑-refl
∪-inl {node _} {node _} = n⊑n (λ _ → ∪-inl)

∪-inr : i ⊑ i' ∪ i
∪-inr {leaf} {_} = l⊑n
∪-inr {node _} {leaf} = ⊑-refl
∪-inr {node _} {node _} = n⊑n (λ _ → ∪-inr)

∪-copair : i ⊑ i'' → i' ⊑ i'' → i ∪ i' ⊑ i''
∪-copair l⊑n q = q
∪-copair (n⊑n f) l⊑n = n⊑n f
∪-copair (n⊑n f) (n⊑n f') = n⊑n (λ op → ∪-copair (f op) (f' op))

lkp : Σₛ → I → I
lkp op leaf = leaf
lkp op (node f) = f op

_[_↦_] : I → Σₛ → I → I
leaf [ _ ↦ _ ] = leaf
node i [ op ↦ v ] = node (λ op' → if op ≡ op' then v else i op')

infix 40 _↓ₑ_
_↓ₑ_ : Σₛ → I → I
op ↓ₑ i = i [ op ↦ leaf ] ∪ lkp op i

infix 40 _↓↓ₑ_
_↓↓ₑ_ : List Σₛ → I → I
[]ₗ ↓↓ₑ i = i
(op ∷ₗ ops) ↓↓ₑ i = op ↓ₑ (ops ↓↓ₑ i)

lkp-↓ₑ-≢ : (i : I) → op ≢ op' → lkp op' i ⊑ lkp op' (op ↓ₑ i)
lkp-↓ₑ-≢ leaf p = l⊑n
lkp-↓ₑ-≢ {op} (node f) p with f op
... | leaf   = subst (_ ⊑_) (sym (ite-≢ p)) ⊑-refl
... | node _ = subst (λ z → _ ⊑ z ∪ _) (sym (ite-≢ p)) ∪-inl

if-mono : i ⊑ i' → if op ≡ op' then leaf else i ⊑ if op ≡ op' then leaf else i'
if-mono {i} {i'} {op} {op'} p with decₛ op op'
... | yes _ = l⊑n
... | no  _ = p

[↦]-mono : i ⊑ i' → i [ op ↦ leaf ] ⊑ i' [ op ↦ leaf ]
[↦]-mono l⊑n = l⊑n
[↦]-mono (n⊑n f) = n⊑n (λ op → if-mono (f op))

lkp-mono : i ⊑ i' → lkp op i ⊑ lkp op i'
lkp-mono l⊑n = l⊑n
lkp-mono (n⊑n f) = f _

↓ₑ-mono : i ⊑ i' → op ↓ₑ i ⊑ op ↓ₑ i'
↓ₑ-mono p = ∪-copair (⊑-trans ([↦]-mono p) ∪-inl) (⊑-trans (lkp-mono p) ∪-inr)

infix 4 _∈ᵢ_
data _∈ᵢ_ : Path → I → Set where
  Hd : []ₗ ∈ᵢ node f
  Tl : p ∈ᵢ f op → op ∷ₗ p ∈ᵢ node f

∈ᵢ-⊑ : i ⊑ i' → p ∈ᵢ i → p ∈ᵢ i'
∈ᵢ-⊑ (n⊑n f) Hd = Hd
∈ᵢ-⊑ (n⊑n f) (Tl v) = Tl (∈ᵢ-⊑ (f _) v)

_∈ᵢ?_ : (p : Path) (i : I) → Dec (p ∈ᵢ i)
p ∈ᵢ? leaf = no (λ ())
[]ₗ ∈ᵢ? node _ = yes Hd
(op ∷ₗ p) ∈ᵢ? node f with p ∈ᵢ? f op
... | yes a = yes (Tl a)
... | no  a = no (λ {(Tl h) → a h})

∈-∪-i₁ : p ∈ᵢ i → p ∈ᵢ i ∪ i'
∈-∪-i₁ {i' = leaf} Hd = Hd
∈-∪-i₁ {i' = node _} Hd = Hd
∈-∪-i₁ {i' = leaf} (Tl u) = Tl u
∈-∪-i₁ {i' = node _} (Tl u) = Tl (∈-∪-i₁ u)

∈-∪-i₂ : p ∈ᵢ i' → p ∈ᵢ i ∪ i'
∈-∪-i₂ {i = leaf} Hd = Hd
∈-∪-i₂ {i = node _} Hd = Hd
∈-∪-i₂ {i = leaf} (Tl u) = Tl (∈-∪-i₂ u)
∈-∪-i₂ {i = node _} (Tl u) = Tl (∈-∪-i₂ u)

∈-∪-e : p ∈ᵢ i ∪ i' → p ∈ᵢ i ⊎ p ∈ᵢ i'
∈-∪-e {i = leaf} u = inj₂ u
∈-∪-e {i = node _} {leaf} u = inj₁ u
∈-∪-e {i = node _} {node _} Hd = inj₁ Hd
∈-∪-e {i = node _} {node _} (Tl u) with ∈-∪-e u
... | inj₁ a = inj₁ (Tl a)
... | inj₂ a = inj₂ (Tl a)

∈ᵢ-lkp-i : op ∷ₗ p ∈ᵢ i → p ∈ᵢ lkp op i
∈ᵢ-lkp-i {i = node x} (Tl u) = u

∈ᵢ-lkp-e : p ∈ᵢ lkp op i → op ∷ₗ p ∈ᵢ i
∈ᵢ-lkp-e {i = node x} u = Tl u 

∈-[↦]-i : ¬ startswith op p → p ∈ᵢ i → p ∈ᵢ i [ op ↦ leaf ]
∈-[↦]-i u Hd = Hd
∈-[↦]-i u (Tl v) = Tl (subst (_ ∈ᵢ_) (sym (ite-≢ λ {refl → u refl})) v)

∈-[↦]-e₁ : p ∈ᵢ i [ op ↦ leaf ] → ¬ startswith op p
∈-[↦]-e₁ {i = node _} Hd ()
∈-[↦]-e₁ {i = node _} (Tl u) refl with () ← subst (_ ∈ᵢ_) ite-≡ u

∈-[↦]-e₂ : p ∈ᵢ i [ op ↦ leaf ] → p ∈ᵢ i
∈-[↦]-e₂ {i = node _} Hd = Hd
∈-[↦]-e₂ {i = node _} {op} (Tl {op = op'} u) with decₛ op op'
... | yes _ with () ← u
... | no  _ = Tl u

∈ᵢ-↓-e : (i : I) → p ∈ᵢ op ↓ₑ i → Σ[ p' ∈ Path ] p' ∈ᵢ i × p ≡ op ↓ p'
∈ᵢ-↓-e i u with ∈-∪-e u
... | inj₂ a = _ , ∈ᵢ-lkp-e a , sym ↓-≡
... | inj₁ a = _ , ∈-[↦]-e₂ a , ↓-≢' (∈-[↦]-e₁ a)

∈ᵢ-↓-i : p ∈ᵢ i → op ↓ p ∈ᵢ op ↓ₑ i
∈ᵢ-↓-i {[]ₗ} u = ∈-∪-i₁ (∈-[↦]-i (λ ()) u)
∈ᵢ-↓-i {op' ∷ₗ p} {op = op} u with decₛ op op'
... | yes refl = ∈-∪-i₂ (∈ᵢ-lkp-i u)
... | no     a = ∈-∪-i₁ (∈-[↦]-i a u)

∈ᵢ-↓↓-e : (q : Path) (i : I) → p ∈ᵢ q ↓↓ₑ i → Σ[ p' ∈ Path ] p' ∈ᵢ i × p ≡ q ↓↓ p'
∈ᵢ-↓↓-e []ₗ i u = _ , u , refl
∈ᵢ-↓↓-e (_ ∷ₗ q) i u with ∈ᵢ-↓-e (q ↓↓ₑ i) u
... | _ , u , refl with ∈ᵢ-↓↓-e q i u
...   | _ , u , refl = _ , u , refl

∈ᵢ-↓↓-i : (q : Path) (i : I) → p ∈ᵢ i → q ↓↓ p ∈ᵢ q ↓↓ₑ i
∈ᵢ-↓↓-i []ₗ i u = u
∈ᵢ-↓↓-i (_ ∷ₗ q) i u = ∈ᵢ-↓-i (∈ᵢ-↓↓-i q i u)

record isfin i : Set where
  field
    paths : Paths
    itop  : (p : Path) → p ∈ᵢ i → p ∈ₚ paths
    ptoi  : (p : Path) → p ∈ₚ paths → p ∈ᵢ i

open isfin

variable
  isf isf' : isfin i

itop-↓ₑ : (isf : isfin i) → p ∈ᵢ op ↓ₑ i → p ∈ₚ op ↓ₚ paths isf
itop-↓ₑ {i} isf u with ∈ᵢ-↓-e i u
... | _ , u , refl = ∈-map-i _ (itop isf _ u)

ptoi-↓ₑ : (isf : isfin i) → p ∈ₚ op ↓ₚ paths isf → p ∈ᵢ op ↓ₑ i
ptoi-↓ₑ isf u with ∈-map-e _ (paths isf) u
... | _ , u , refl = ∈ᵢ-↓-i (ptoi isf _ u)

fin-↓ₑ : (op : Σₛ) → isfin i → isfin (op ↓ₑ i)
fin-↓ₑ op isf =
  record {
    paths = op ↓ₚ paths isf ;
    itop  = λ _ → itop-↓ₑ isf ;
    ptoi  = λ _ → ptoi-↓ₑ isf
  }

fin-lkp : (op : Σₛ) → isfin i → isfin (lkp op i)
fin-lkp op isf =
  record {
    paths = lkpₚ op (paths isf) ;
    itop = λ p x → ∈-lkp-i _ (itop isf _ (∈ᵢ-lkp-e x)) ;
    ptoi = λ p x → ∈ᵢ-lkp-i (ptoi isf _ (∈-lkp-e _ x))
  }

∣_∣ : isfin i → ℕ
∣ isf ∣ = len (paths isf)

size-↓ₑ-≤ : (isf : isfin i) → ∣ fin-↓ₑ op isf ∣ ≤ ∣ isf ∣
size-↓ₑ-≤ isf = len-map-≤ _ (paths isf)

[]∈ᵢ : p ∈ᵢ i → []ₗ ∈ᵢ i
[]∈ᵢ Hd = Hd
[]∈ᵢ (Tl u) = Hd

∈ᵢ-startswith : p ∈ᵢ i → ¬ [ op ]ₗ ∈ᵢ i → ¬ startswith op p
∈ᵢ-startswith (Tl u) v refl = v (Tl ([]∈ᵢ u))

size-↓ₑ-< : (isf : isfin i) → [ op ]ₗ ∈ᵢ i → ∣ fin-↓ₑ op isf ∣ < ∣ isf ∣
size-↓ₑ-< isf u = len-↓ₚ-< (itop isf _ ([]∈ᵢ u)) (itop isf _ u)

size-↓ₑ-≡ : (isf : isfin i) → ¬ [ op ]ₗ ∈ᵢ i → ∣ fin-↓ₑ op isf ∣ ≡ ∣ isf ∣
size-↓ₑ-≡ isf u = len-↓ₚ-≡ (λ x → ∈ᵢ-startswith (ptoi isf _ x) u)

itop-↓↓ₑ : (isf : isfin i) → p ∈ᵢ q ↓↓ₑ i → p ∈ₚ q ↓↓ₚ paths isf
itop-↓↓ₑ {q = q} isf u with ∈ᵢ-↓↓-e q _ u
... | _ , u , refl = ∈-map-i _ (itop isf _ u)

ptoi-↓↓ₑ : (isf : isfin i) → p ∈ₚ q ↓↓ₚ paths isf → p ∈ᵢ q ↓↓ₑ i
ptoi-↓↓ₑ {q = q} isf u with ∈-map-e _ (paths isf) u
... | _ , u , refl = ∈ᵢ-↓↓-i q _ (ptoi isf _ u)

fin-↓↓ₑ : (q : Path) → isfin i → isfin (q ↓↓ₑ i)
fin-↓↓ₑ []ₗ isf = isf
fin-↓↓ₑ (op ∷ₗ q) isf = fin-↓ₑ op (fin-↓↓ₑ q isf)

size-↓↓ₑ : (isf : isfin i) (q : Path) → ∣ fin-↓↓ₑ q isf ∣ ≡ len (q ↓↓ₚ paths isf)
size-↓↓ₑ isf q =
  ≤-antisym
    (len-⊑ (λ x → itop-↓↓ₑ {q = q} isf (ptoi (fin-↓↓ₑ q isf) _ x)))
    (len-⊑ (λ x → itop (fin-↓↓ₑ q isf) _ (ptoi-↓↓ₑ {q = q} isf x)))

size-↓↓ₑ-≤ : (isf : isfin i) → ∣ fin-↓↓ₑ q isf ∣ ≤ ∣ isf ∣
size-↓↓ₑ-≤ {i} {q} isf rewrite size-↓↓ₑ isf q = len-map-≤ _ (paths isf)