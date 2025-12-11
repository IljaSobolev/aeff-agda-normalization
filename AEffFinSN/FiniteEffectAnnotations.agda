open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties as NatProp using
  (+-comm; +-assoc; +-monoʳ-≤; +-mono-≤; +-identityʳ; ≤-reflexive; ≤-refl; ≤-antisym; ≤-trans; n≤1+n; +-suc; <⇒≤)
open import Data.Nat.ListAction using (sum)
open import Data.List using (List) renaming ([] to []ₗ; _∷_ to _∷ₗ_)

open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; cong; sym; trans; _≢_)

open import Function using (id; _∘_)

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


-- FINITE SUBSETS OF Σₛ AND THEIR PROPERTIES

data Ops : Set

_#_ : Σₛ → Ops → Set

data Ops where
  []   : Ops
  cons : (op : Σₛ) (ops : Ops) → op # ops → Ops

infix 4 _#_
op # [] = ⊤
op # cons op' as _ = op ≢ op' × op # as

variable
  ops ops' ops'' : Ops

_#?_ : (op : Σₛ) (ops : Ops) → Dec (op # ops)
op #? [] = yes tt
op #? cons op' ops x with decₛ op op'
... | yes p = no (λ (q , _) → q p)
... | no  p with op #? ops
...   | yes q = yes (p , q)
...   | no  q = no (λ (_ , p) → q p)

_++_ : Ops → Ops → Ops

#-++-i : (ops ops' : Ops) → op # ops → op # ops' → op # ops ++ ops'

[] ++ ops' = ops'
cons op ops x ++ ops' with op #? ops'
... | yes a = cons op (ops ++ ops') (#-++-i _ _ x a)
... | no  _ = ops ++ ops'

#-++-i [] _ _ q = q
#-++-i (cons op _ _) ops' (p , r) q with op #? ops'
... | yes _ = p , #-++-i _ _ r q
... | no  _ = #-++-i _ _ r q

#-++-e₂ : (ops ops' : Ops) → op # ops ++ ops' → op # ops'
#-++-e₂ [] _ p = p
#-++-e₂ (cons op ops _) ops' p with op #? ops'
... | yes _ = #-++-e₂ ops _ (proj₂ p)
... | no  _ = #-++-e₂ ops _ p

#-++-e₁ : (ops ops' : Ops) → op # ops ++ ops' → op # ops
#-++-e₁ [] _ _ = tt
#-++-e₁ (cons op ops _) ops' p with op #? ops'
... | yes _ with p , q ← p = p , #-++-e₁ _ _ q
... | no  a = (λ {refl → a (#-++-e₂ ops _ p)}) , #-++-e₁ _ _ p

delete : Ops → Σₛ → Ops

#-delete-i₁ : (ops : Ops) → op' # ops → op' # delete ops op

delete [] op = []
delete (cons op' ops x) op with decₛ op op'
... | yes _ = ops
... | no  _ = cons op' (delete ops op) (#-delete-i₁ _ x)

#-delete-i₁ [] p = p
#-delete-i₁ {op''} {op} (cons op' ops x) (p , q) with decₛ op op'
... | yes _ = q
... | no  _ = p , #-delete-i₁ _ q

#-delete-i₂ : (ops : Ops) → op # delete ops op
#-delete-i₂ [] = tt
#-delete-i₂ {op} (cons op' ops x) with decₛ op op'
... | yes refl = x
... | no     a = a , #-delete-i₂ ops

#-delete-e : (ops : Ops) → op' # delete ops op → op' ≡ op ⊎ op' # ops
#-delete-e [] p = inj₂ tt
#-delete-e {op'} {op} (cons op'' ops x) p with decₛ op op'' | decₛ op' op''
... | yes refl | yes p = inj₁ p
... | yes refl | no  a = inj₂ (a , p)
... | no     _ | _ with p , q ← p = [ inj₁ , inj₂ ∘ (p ,_) ]′ (#-delete-e _ q)

_⧵_ : Ops → Ops → Ops
ops ⧵ [] = ops
ops ⧵ cons op ops' _ = delete ops op ⧵ ops'

#-⧵-i₁ : (ops ops' : Ops) → op # ops → op # ops ⧵ ops'
#-⧵-i₁ _ [] p = p
#-⧵-i₁ _ (cons _ ops' _) p = #-⧵-i₁ _ ops' (#-delete-i₁ _ p)

∈-cons : {x : op' # ops} → ¬ op # cons op' ops x → op ≡ op' ⊎ ¬ op # ops
∈-cons {op'} {ops} {op} p with decₛ op op'
... | yes a = inj₁ a
... | no  a = inj₂ (p ∘ (a ,_))

#-⧵-i₂ : (ops ops' : Ops) → ¬ op # ops' → op # ops ⧵ ops'
#-⧵-i₂ _ [] p = ⊥-elim (p tt)
#-⧵-i₂ ops (cons _ ops' x) p with ∈-cons {x = x} p
... | inj₁ refl = #-⧵-i₁ _ ops' (#-delete-i₂ ops)
... | inj₂ a = #-⧵-i₂ _ _ a

#-⧵-e : (ops ops' : Ops) → op # ops ⧵ ops' → op # ops ⊎ ¬ op # ops'
#-⧵-e _ [] p = inj₁ p
#-⧵-e _ (cons _ _ _) p with #-⧵-e _ _ p
... | inj₂ a = inj₂ (a ∘ proj₂)
... | inj₁ a with #-delete-e _ a
...   | inj₁ a = inj₂ (λ (z , _) → z a)
...   | inj₂ a = inj₁ a

infix 4 _⊆_
_⊆_ : Ops → Ops → Set
ops ⊆ ops' = {op : Σₛ} → op # ops' → op # ops

_##_ : Ops → Ops → Set
[] ## ops' = ⊤
cons op ops _ ## ops' = op # ops' × ops ## ops'

##-⧵ : (ops ops' : Ops) → ops ## (ops' ⧵ ops)
##-⧵ [] _ = tt
##-⧵ (cons _ ops _) ops' = #-⧵-i₁ _ ops (#-delete-i₂ ops') , ##-⧵ _ _

++-⧵ : (ops ops' : Ops) → op # ops ++ (ops' ⧵ ops) → op # ops ++ ops'
++-⧵ ops _ p = #-++-i ops _ (#-++-e₁ _ _ p) ([ id , (λ z → ⊥-elim (z (#-++-e₁ _ _ p))) ]′ (#-⧵-e _ ops (#-++-e₂ ops _ p)))

⧵-++ : (ops ops' : Ops) → op # ops ++ ops' → op # ops ++ (ops' ⧵ ops)
⧵-++ ops _ p = #-++-i ops _ (#-++-e₁ _ _ p) (#-⧵-i₁ _ ops (#-++-e₂ ops _ p))

delete-mono : (ops ops' : Ops) → ops ⊆ ops' → delete ops op ⊆ delete ops' op
delete-mono ops _ p q with #-delete-e _ q
... | inj₁ a rewrite a = #-delete-i₂ ops
... | inj₂ a = #-delete-i₁ _ (p a)

⊆-trans : ops ⊆ ops' → ops' ⊆ ops'' → ops ⊆ ops''
⊆-trans p = p ∘_

delete-cons : {x : op # ops} → ops ⊆ delete (cons op ops x) op
delete-cons {op} p with decₛ op op
... | yes refl = p
... | no     a = ⊥-elim (a refl)

++-comm : (ops ops' : Ops) → ops ++ ops' ⊆ ops' ++ ops
++-comm _ ops' p = #-++-i _ _ (#-++-e₂ ops' _ p) (#-++-e₁ _ _ p)


-- INTERRUPT EFFECT ANNOTATIONS

data I : Set where
  leaf : I
  node : (Σₛ → I) → I

variable
  i i' i'' i''' : I
  f g : Σₛ → I

infix 10 _⊑i_
data _⊑i_ : I → I → Set where
  l⊑n : leaf ⊑i i
  n⊑n : ((op : Σₛ) → f op ⊑i g op) → node f ⊑i node g

⊑i-refl : i ⊑i i
⊑i-refl {leaf} = l⊑n
⊑i-refl {node _} = n⊑n (λ _ → ⊑i-refl)

⊑i-trans : i ⊑i i' → i' ⊑i i'' → i ⊑i i''
⊑i-trans l⊑n q = l⊑n
⊑i-trans (n⊑n f) (n⊑n f') = n⊑n (λ op → ⊑i-trans (f op) (f' op))

infix 15 _∪_
_∪_ : I → I → I
leaf ∪ i = i
node f ∪ leaf = node f
node f ∪ node g = node (λ op → f op ∪ g op)

∪-inl : i ⊑i i ∪ i'
∪-inl {leaf} {_} = l⊑n
∪-inl {node _} {leaf} = ⊑i-refl
∪-inl {node _} {node _} = n⊑n (λ _ → ∪-inl)

∪-inr : i ⊑i i' ∪ i
∪-inr {leaf} {_} = l⊑n
∪-inr {node _} {leaf} = ⊑i-refl
∪-inr {node _} {node _} = n⊑n (λ _ → ∪-inr)

∪-copair : i ⊑i i'' → i' ⊑i i'' → i ∪ i' ⊑i i''
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
(op ∷ₗ ops) ↓↓ₑ i = ops ↓↓ₑ (op ↓ₑ i)

↓ₑ-⊑i : lkp op i ⊑i op ↓ₑ i
↓ₑ-⊑i {i = leaf} = l⊑n
↓ₑ-⊑i {i = node _} = ∪-inr

lkp-↓ₑ-≢ : op ≢ op' → lkp op' i ⊑i lkp op' (op ↓ₑ i)
lkp-↓ₑ-≢ {i = leaf} p = l⊑n
lkp-↓ₑ-≢ {op} {i = node f} p with f op
... | leaf   = subst (_ ⊑i_) (sym (ite-≢ p)) ⊑i-refl
... | node _ = subst (λ z → _ ⊑i z ∪ _) (sym (ite-≢ p)) ∪-inl

if-mono : i ⊑i i' → if op ≡ op' then leaf else i ⊑i if op ≡ op' then leaf else i'
if-mono {i} {i'} {op} {op'} p with decₛ op op'
... | yes _ = l⊑n
... | no  _ = p

[↦]-mono : i ⊑i i' → i [ op ↦ leaf ] ⊑i i' [ op ↦ leaf ]
[↦]-mono l⊑n = l⊑n
[↦]-mono (n⊑n f) = n⊑n (λ op → if-mono (f op))

lkp-mono : i ⊑i i' → lkp op i ⊑i lkp op i'
lkp-mono l⊑n = l⊑n
lkp-mono (n⊑n f) = f _

↓ₑ-mono : i ⊑i i' → op ↓ₑ i ⊑i op ↓ₑ i'
↓ₑ-mono p = ∪-copair (⊑i-trans ([↦]-mono p) ∪-inl) (⊑i-trans (lkp-mono p) ∪-inr)


-- FINITENESS

isleaf : I → Set
isleaf i = i ≡ leaf

isnode : I → Set
isnode i = ¬ isleaf i

isfin : I → Set

record Finite f : Set where
  inductive
  field
    cfin : (op : Σₛ) → isfin (f op)
    list : Ops
    to   : (op : Σₛ) → op # list → isleaf (f op)
    from : (op : Σₛ) → isleaf (f op) → op # list

open Finite

isfin leaf = ⊤
isfin (node f) = Finite f

variable
  isf isf' : isfin i'

isleaf-∪ : isleaf i → isleaf i' → isleaf (i ∪ i')
isleaf-∪ refl refl = refl

∪-isleaf₁ : isleaf (i ∪ i') → isleaf i
∪-isleaf₁ {leaf} p = refl
∪-isleaf₁ {node _} {leaf} p = p

∪-isleaf₂ : isleaf (i ∪ i') → isleaf i'
∪-isleaf₂ {i} {leaf} p = refl
∪-isleaf₂ {leaf} {node _} p = p

fin-∪ : isfin i → isfin i' → isfin (i ∪ i')
fin-∪ {leaf} _ isf' = isf'
fin-∪ {node _} {leaf} isf _ = isf
fin-∪ {node f} {node g} isf isf' =
  record {
    cfin = λ op → fin-∪ (cfin isf op) (cfin isf' op) ;
    list = list isf ++ list isf' ;
    to = λ op p → isleaf-∪ (to isf op (#-++-e₁ _ _ p)) (to isf' op (#-++-e₂ (list isf) _ p)) ;
    from = λ op p → #-++-i _ _ (from isf op (∪-isleaf₁ p)) (from isf' op (∪-isleaf₂ p))
  }

fin-lkp : (op : Σₛ) → isfin i → isfin (lkp op i)
fin-lkp {leaf} op isf = tt
fin-lkp {node _} op isf = cfin isf op

fin-if : (op op' : Σₛ) → isfin i → isfin (if op ≡ op' then leaf else i)
fin-if op op' isf with decₛ op op'
... | yes _ = tt
... | no  _ = isf

isleaf-⊑i : i ⊑i i' → isleaf i' → isleaf i
isleaf-⊑i {i' = leaf} l⊑n q = q

isnode-⊑i : i ⊑i i' → isnode i → isnode i'
isnode-⊑i p q = q ∘ isleaf-⊑i p

isleaf-if : isleaf i → isleaf (if op ≡ op' then leaf else i)
isleaf-if {i} {op} {op'} p with decₛ op op'
... | yes _ = refl
... | no  _ = p

if-isleaf : isleaf (if op ≡ op' then leaf else i) → op ≡ op' ⊎ isleaf i
if-isleaf {op} {op'} {i} p with decₛ op op'
... | yes a = inj₁ a
... | no  _ = inj₂ p

fin-[↦] : (op : Σₛ) → isfin i → isfin (i [ op ↦ leaf ])
fin-[↦] {leaf} op isf = tt
fin-[↦] {node f} op isf =
  record {
    cfin = λ op' → fin-if op op' (cfin isf op') ;
    list = delete (list isf) op ;
    to = λ op' p → [ (λ {refl → ite-≡}) , (λ q → isleaf-if (to isf op' q)) ]′ (#-delete-e _ p) ;
    from = λ op' p → [ (λ {refl → #-delete-i₂ (list isf)}) , (λ q → #-delete-i₁ _ (from isf op' q)) ]′ (if-isleaf p)
  }

fin-↓ₑ : (op : Σₛ) → isfin i → isfin (op ↓ₑ i)
fin-↓ₑ op isf = fin-∪ (fin-[↦] op isf) (fin-lkp op isf)

fin-↓↓ₑ : (ops : List Σₛ) → isfin i → isfin (ops ↓↓ₑ i)
fin-↓↓ₑ []ₗ isf = isf
fin-↓↓ₑ (op ∷ₗ ops) isf = fin-↓↓ₑ ops (fin-↓ₑ op isf)

map : (Σₛ → A) → Ops → List A
map f [] = []ₗ
map f (cons op ops _) = f op ∷ₗ map f ops

sum-map-disj : {f : Σₛ → ℕ} (ops ops' : Ops) → ops ## ops' → sum (map f (ops ++ ops')) ≡ sum (map f ops) + sum (map f ops')
sum-map-disj [] ops' _ = refl
sum-map-disj {f} (cons op ops _) ops' (p , q) with op #? ops'
... | yes _ = trans (cong (f op +_) (sum-map-disj ops ops' q)) (sym (+-assoc (f op) _ _))
... | no  a = ⊥-elim (a p)

+-lemma : (n m k : ℕ) → n + (m + k) ≡ m + (n + k)
+-lemma n m k = trans (sym (+-assoc n _ _)) (trans (cong (_+ k) (+-comm n _)) (+-assoc m _ _))

sum-map-delete : {f : Σₛ → ℕ} (ops : Ops) → ¬ op # ops → sum (map f ops) ≡ f op + sum (map f (delete ops op))
sum-map-delete [] p = ⊥-elim (p tt)
sum-map-delete {op} {f} (cons op' ops x) p with decₛ op op'
... | yes refl = refl
... | no     a = trans (cong (f op' +_) (sum-map-delete _ (p ∘ (a ,_)))) (+-lemma (f op') (f op) _)

sum-mono-⊆ : {f : Σₛ → ℕ} (ops ops' : Ops) → ops ⊆ ops' → sum (map f ops) ≤ sum (map f ops')
sum-mono-⊆ [] _ _ = z≤n
sum-mono-⊆ {f} (cons op ops x) ops' p =
  begin
    f op + sum (map f ops)
  ≤⟨ +-monoʳ-≤ _ (sum-mono-⊆ _ _ (⊆-trans delete-cons (delete-mono (cons op ops x) _ p))) ⟩
    f op + sum (map f (delete ops' op))
  ≡⟨ sym (sum-map-delete _ (λ z → proj₁ (p z) refl)) ⟩
    sum (map f ops')
  ∎
  where open NatProp.≤-Reasoning

sum-mono-≈ : {f : Σₛ → ℕ} (ops ops' : Ops) → ops ⊆ ops' → ops' ⊆ ops → sum (map f ops) ≡ sum (map f ops')
sum-mono-≈ _ _ p q = ≤-antisym (sum-mono-⊆ _ _ p) (sum-mono-⊆ _ _ q)

sum-mono-≤ : {f g : Σₛ → ℕ} (ops : Ops) → ({op : Σₛ} → ¬ op # ops → f op ≤ g op) → sum (map f ops) ≤ sum (map g ops)
sum-mono-≤ [] _ = z≤n
sum-mono-≤ (cons _ _ _) mono = +-mono-≤ (mono (λ z → proj₁ z refl)) (sum-mono-≤ _ (λ z → mono (z ∘ proj₂)))

sum-≡ : {f g : Σₛ → ℕ} (ops : Ops) → ({op : Σₛ} → ¬ op # ops → f op ≡ g op) → sum (map f ops) ≡ sum (map g ops)
sum-≡ _ eq = ≤-antisym (sum-mono-≤ _ (≤-reflexive ∘ eq)) (sum-mono-≤ _ (≤-reflexive ∘ sym ∘ eq))

∣_∣ : isfin i → ℕ
∣_∣ {leaf} p = zero
∣_∣ {node f} p = suc (sum (map (λ op → ∣ cfin p op ∣) (list p)))

isf-disj : (isf : Finite f) → op # list isf → ∣ cfin isf op ∣ ≡ 0
isf-disj {f} {op} isf p with _ ← cfin isf op rewrite to isf op p = refl

sum-zero : (ops : Ops) → sum (map (λ _ → 0) ops) ≡ 0
sum-zero [] = refl
sum-zero (cons op ops x) = sum-zero ops

¬∈→# : ¬ ¬ op # ops → op # ops
¬∈→# {op} {ops} p with op #? ops
... | yes a = a
... | no  a = ⊥-elim (p a)

sum-lemma : (isf : Finite f) (isf' : Finite g) →
            ------------------------------------
            sum (map (λ op → ∣ cfin isf op ∣) (list isf ++ list isf'))
            ≡
            sum (map (λ op → ∣ cfin isf op ∣) (list isf))
sum-lemma {f} {g} isf isf' = let lf = list isf; lf' = list isf'; e = λ op → ∣ cfin isf op ∣ in
  begin
    sum (map e (lf ++ lf'))
  ≡⟨ sum-mono-≈ _ _ (++-⧵ lf lf') (⧵-++ lf lf') ⟩
    sum (map e (lf ++ (lf' ⧵ lf)))
  ≡⟨ sum-map-disj lf _ (##-⧵ _ _) ⟩
    sum (map e lf) + sum (map e (lf' ⧵ lf))
  ≡⟨ cong (_ +_) (sum-≡ _ (λ p → isf-disj isf (¬∈→# (p ∘ (#-⧵-i₂ _ _))))) ⟩
    sum (map e lf) + sum (map (λ _ → 0) (lf' ⧵ lf))
  ≡⟨ cong (_ +_) (sum-zero (lf' ⧵ lf)) ⟩
    sum (map e lf) + 0
  ≡⟨ +-identityʳ _ ⟩
    sum (map e lf)
  ∎
  where open Eq.≡-Reasoning

+-lemma' : (n m l k : ℕ) → n + m + (l + k) ≡ n + l + (m + k)
+-lemma' n m l k = trans (+-assoc n _ _) (trans (cong (n +_) (+-lemma m l _)) (sym (+-assoc n _ _)))

sum-+ : {f g : Σₛ → ℕ} (ops : Ops) → sum (map (λ x → f x + g x) ops) ≡ sum (map f ops) + sum (map g ops)
sum-+ [] = refl
sum-+ {f} (cons op ops _) = trans (cong (_ +_) (sum-+ ops)) (+-lemma' (f op) _ _ _)

size-∪ : (isf : isfin i) (isf' : isfin i') → ∣ fin-∪ isf isf' ∣ ≤ ∣ isf ∣ + ∣ isf' ∣
size-∪ {leaf} _ _ = ≤-refl
size-∪ {node _} {leaf} isf _ rewrite +-identityʳ (suc (sum (map (λ op → ∣ cfin isf op ∣) (list isf)))) = ≤-refl
size-∪ {node f} {node g} isf isf' = let lf = list isf; lf' = list isf'; cf = λ op → ∣ cfin isf op ∣; cf' = λ op → ∣ cfin isf' op ∣ in s≤s (
  begin
    sum (map (λ op → ∣ fin-∪ (cfin isf op) (cfin isf' op) ∣) (lf ++ lf'))
  ≤⟨ sum-mono-≤ (lf ++ lf') (λ _ → size-∪ (cfin isf _) _) ⟩
    sum (map (λ op → ∣ cfin isf op ∣ + ∣ cfin isf' op ∣) (lf ++ lf'))
  ≡⟨ sum-+ (lf ++ lf') ⟩
    sum (map cf (lf ++ lf')) + sum (map cf' (lf ++ lf'))
  ≡⟨ cong (_+ _) (sum-lemma isf isf') ⟩
    sum (map cf lf) + sum (map cf' (lf ++ lf'))
  ≡⟨ cong (_ +_) (sum-mono-≈ _ _ (++-comm lf _) (++-comm lf' _)) ⟩
    sum (map cf lf) + sum (map cf' (lf' ++ lf))
  ≡⟨ cong (_ +_) (sum-lemma isf' isf) ⟩
    sum (map cf lf) + sum (map cf' lf')
  ≤⟨ +-monoʳ-≤ _ (n≤1+n _) ⟩
    sum (map cf lf) + suc (sum (map cf' lf'))
  ∎)
  where open NatProp.≤-Reasoning

size-∪-< : (isf : isfin i) (isf' : isfin i') → isnode i → isnode i' → ∣ fin-∪ isf isf' ∣ < ∣ isf ∣ + ∣ isf' ∣
size-∪-< {leaf} _ _ p _ = ⊥-elim (p refl)
size-∪-< {node _} {leaf} _ _ _ q = ⊥-elim (q refl)
size-∪-< {node f} {node g} isf isf' _ _ = let lf = list isf; lf' = list isf'; cf = λ op → ∣ cfin isf op ∣; cf' = λ op → ∣ cfin isf' op ∣ in s≤s (
  begin
    suc (sum (map (λ op → ∣ fin-∪ (cfin isf op) (cfin isf' op) ∣) (lf ++ lf')))
  ≤⟨ s≤s (sum-mono-≤ (lf ++ lf') (λ _ → size-∪ (cfin isf _) _)) ⟩
    suc (sum (map (λ op → ∣ cfin isf op ∣ + ∣ cfin isf' op ∣) (lf ++ lf')))
  ≡⟨ cong suc (sum-+ (lf ++ lf')) ⟩
    suc (sum (map cf (lf ++ lf')) + sum (map cf' (lf ++ lf')))
  ≡⟨ cong suc (cong (_+ _) (sum-lemma isf isf')) ⟩
    suc (sum (map cf lf) + sum (map cf' (lf ++ lf')))
  ≡⟨ cong suc (cong (_ +_) (sum-mono-≈ _ _ (++-comm lf _) (++-comm lf' _))) ⟩
    suc (sum (map cf lf) + sum (map cf' (lf' ++ lf)))
  ≡⟨ cong suc (cong (_ +_) (sum-lemma isf' isf)) ⟩
    suc (sum (map cf lf) + sum (map cf' lf'))
  ≡⟨ sym (+-suc _ _) ⟩
    sum (map cf lf) + suc (sum (map cf' lf'))
  ∎)
  where open NatProp.≤-Reasoning

fin-if-≢ : (isf : isfin i) → op ≢ op' → ∣ fin-if op op' isf ∣ ≡ ∣ isf ∣
fin-if-≢ {i} {op} {op'} isf p with decₛ op op'
... | yes a = ⊥-elim (p a)
... | no  _ = refl

size-[↦]-lkp : (isf : isfin i) → isnode (lkp op i) → ∣ fin-[↦] op isf ∣ + ∣ fin-lkp op isf ∣ ≡ ∣ isf ∣
size-[↦]-lkp {leaf} isf p = ⊥-elim (p refl)
size-[↦]-lkp {node _} {op} isf p = let lf = list isf in cong suc (
  begin
    sum (map (λ op' → ∣ fin-if op op' (cfin isf op') ∣) (delete lf op)) + ∣ cfin isf op ∣
  ≡⟨ cong (_+ ∣ cfin isf op ∣) (sum-≡ (delete lf op) (λ p → fin-if-≢ (cfin isf _) (λ {refl → p (#-delete-i₂ lf)}))) ⟩
    sum (map (λ op → ∣ cfin isf op ∣) (delete lf op)) + ∣ cfin isf op ∣
  ≡⟨ +-comm _ ∣ cfin isf op ∣ ⟩
    ∣ cfin isf op ∣ + sum (map (λ op → ∣ cfin isf op ∣) (delete lf op))
  ≡⟨ sym (sum-map-delete _ (p ∘ to isf op)) ⟩
    sum (map (λ op → ∣ cfin isf op ∣) lf)
  ∎)
  where open Eq.≡-Reasoning

size-[↦]-lkp-leaf : (isf : isfin i) → isleaf (lkp op i) → ∣ fin-[↦] op isf ∣ + ∣ fin-lkp op isf ∣ ≤ ∣ isf ∣
size-[↦]-lkp-leaf {leaf} isf p = z≤n
size-[↦]-lkp-leaf {node x} {op} isf p = let lf = list isf in s≤s (
  begin
    sum (map (λ op' → ∣ fin-if op op' (cfin isf op') ∣) (delete lf op)) + ∣ cfin isf op ∣
  ≡⟨ cong (_+ ∣ cfin isf op ∣) (sum-≡ (delete lf op) (λ p → fin-if-≢ (cfin isf _) (λ {refl → p (#-delete-i₂ lf)}))) ⟩
    sum (map (λ op → ∣ cfin isf op ∣) (delete lf op)) + ∣ cfin isf op ∣
  ≡⟨ +-comm _ ∣ cfin isf op ∣ ⟩
    ∣ cfin isf op ∣ + sum (map (λ op → ∣ cfin isf op ∣) (delete lf op))
  ≡⟨ cong (_+ sum (map (λ op → ∣ cfin isf op ∣) (delete lf op))) (isf-disj isf (from isf _ p)) ⟩
    sum (map (λ op → ∣ cfin isf op ∣) (delete lf op))
  ≤⟨ sum-mono-⊆ (delete lf op) lf (#-delete-i₁ lf) ⟩
    sum (map (λ op → ∣ cfin isf op ∣) lf)
  ∎)
  where open NatProp.≤-Reasoning

lkp-isnode : isnode (lkp op i) → isnode i
lkp-isnode {op} {leaf} p = p

[↦]-isnode : isnode i → isnode (i [ op ↦ i' ])
[↦]-isnode {leaf} p = p

size-↓ₑ-leaf : (isf : isfin i) → isleaf (lkp op i) → ∣ fin-↓ₑ op isf ∣ ≤ ∣ isf ∣
size-↓ₑ-leaf {i} {op} isf p = ≤-trans (size-∪ (fin-[↦] op isf) _) (size-[↦]-lkp-leaf isf p)

l⊎n : (i : I) → isleaf i ⊎ isnode i
l⊎n leaf = inj₁ refl
l⊎n (node _) = inj₂ (λ ())

size-↓ₑ-< : (isf : isfin i) → isnode (lkp op i) → ∣ fin-↓ₑ op isf ∣ < ∣ isf ∣
size-↓ₑ-< isf p = ≤-trans (size-∪-< _ _ ([↦]-isnode (lkp-isnode p)) p) (≤-reflexive (size-[↦]-lkp isf p))

size-↓ₑ : (isf : isfin i) → ∣ fin-↓ₑ op isf ∣ ≤ ∣ isf ∣
size-↓ₑ {leaf} {op} isf = z≤n
size-↓ₑ {node f} {op} isf with l⊎n (f op)
... | inj₁ p = size-↓ₑ-leaf isf p
... | inj₂ p = <⇒≤ (size-↓ₑ-< isf p)

size-⊑i : (isf : isfin i) (isf' : isfin i') → i ⊑i i' → ∣ isf ∣ ≤ ∣ isf' ∣
size-⊑i isf isf' l⊑n = z≤n
size-⊑i isf isf' (n⊑n f) = s≤s (
  begin
    sum (map (λ op → ∣ cfin isf op ∣) (list isf))
  ≤⟨ sum-mono-≤ (list isf) (λ _ → size-⊑i _ _ (f _)) ⟩
    sum (map (λ op → ∣ cfin isf' op ∣) (list isf))
  ≤⟨ sum-mono-⊆ _ _ (λ u → from isf _ (isleaf-⊑i (f _) (to isf' _ u))) ⟩
    sum (map (λ op → ∣ cfin isf' op ∣) (list isf'))
  ∎)
  where open NatProp.≤-Reasoning

⊑i-lemma : i ∪ i' ⊑i (i ∪ i'') ∪ (i' ∪ i''')
⊑i-lemma {i} {i'} {i''} {i'''} = ∪-copair {i} {_} {i'} (⊑i-trans ∪-inl ∪-inl) (⊑i-trans ∪-inl (∪-inr {i' ∪ i'''} {i ∪ i''}))

⊑i-lemma' : i ∪ i' ⊑i (i'' ∪ i) ∪ (i''' ∪ i')
⊑i-lemma' {i} {i'} {i''} {i'''} = ∪-copair {i} {_} {i'} (⊑i-trans (∪-inr {i} {i''}) ∪-inl) (⊑i-trans ∪-inr (∪-inr {i''' ∪ i'} {i'' ∪ i}))

if-distrib-∪₁ : if op ≡ op' then i else (i' ∪ i'') ⊑i if op ≡ op' then i else i' ∪ if op ≡ op' then i else i''
if-distrib-∪₁ {op} {op'} with decₛ op op'
... | yes _ = ∪-inl
... | no  _ = ⊑i-refl

[↦]-distrib-∪₁ : (i ∪ i') [ op ↦ leaf ] ⊑i i [ op ↦ leaf ] ∪ i' [ op ↦ leaf ]
[↦]-distrib-∪₁ {leaf} = ⊑i-refl
[↦]-distrib-∪₁ {node _} {leaf} = ⊑i-refl
[↦]-distrib-∪₁ {node _} {node _} = n⊑n (λ _ → if-distrib-∪₁)

lkp-distrib-∪₁ : lkp op (i ∪ i') ⊑i lkp op i ∪ lkp op i'
lkp-distrib-∪₁ {op} {leaf} = ⊑i-refl
lkp-distrib-∪₁ {op} {node _} {leaf} = ∪-inl
lkp-distrib-∪₁ {op} {node _} {node _} = ⊑i-refl

↓ₑ-distrib-∪₁ : op ↓ₑ (i ∪ i') ⊑i op ↓ₑ i ∪ op ↓ₑ i'
↓ₑ-distrib-∪₁ {op} {i} {i'} =
  ∪-copair
    (⊑i-trans ([↦]-distrib-∪₁ {i} {i'}) (⊑i-lemma {i [ op ↦ leaf ]}))
    (⊑i-trans (lkp-distrib-∪₁ {_} {i} {i'}) (⊑i-lemma' {i'' = i [ op ↦ leaf ]}))