{-# OPTIONS --guardedness #-}

open import Data.Bool hiding (if_then_else_)
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.Maybe
open import Data.Product renaming (proj₁ to pr₁; proj₂ to pr₂)
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module AEffReinstSN.CoinductiveEffectAnnotations where

open import Axiom.Extensionality.Propositional


-- ASSUMING FUNCTION EXTENSIONALITY

postulate
  fun-ext : ∀ {a b} → Extensionality a b
  ifun-ext : ∀ {a b} → ExtensionalityImplicit a b


-- SIGNAL AND INTERRUPT NAMES

postulate Σₛ : Set

variable
  op op' op'' : Σₛ
  ops ops' : List Σₛ

postulate decₛ : (op op' : Σₛ) → Dec (op ≡ op')

if_≡_then_else_ : {A : Set} → Σₛ → Σₛ → A → A → A
if op ≡ op' then x else y with decₛ op op'
... | yes p = x
... | no ¬p = y


ite-≡ : {A : Set} {x y : A} →
        -----------------------------
        if op ≡ op then x else y ≡ x
ite-≡ {op} with decₛ op op
... | yes p = refl
... | no ¬p = ⊥-elim (¬p refl)


ite-≢ : {A : Set} {x y : A} →
        op ≢ op' →
        ------------------------------
        if op ≡ op' then x else y ≡ y

ite-≢ {op} {op'} p with decₛ op op'
... | yes q = ⊥-elim (p q)
... | no ¬q = refl

-- EFFECT ANNOTATIONS FOR OUTGOING SIGNALS (O) AND INTERRUPT HANDLERS (I)

data O : Set where
  omap : (Σₛ → Maybe ⊤) → O

variable
  o o' o'' o''' : O

record I : Set where
  coinductive
  constructor
    ic
  field
    imap : Σₛ → Maybe (O × I)

open I public

variable
  i i' i'' i''' : I

-- EMPTY EFFECT ANNOTATIONS

∅ₒ : O
∅ₒ = omap (λ _ → nothing)

∅ᵢ : I
imap ∅ᵢ op = nothing


-- UNION OF EFFECT ANNOTATIONS

_∪ₒ_ : O → O → O
(omap o) ∪ₒ (omap o') = omap (λ op → o op <∣> o' op)

_∪ᵢ_ : I → I → I

_∪-aux_ : Maybe (O × I) → Maybe (O × I) → Maybe (O × I)

_∪-aux_ nothing oi = oi
_∪-aux_ (just oi) nothing = just oi
_∪-aux_ (just (o , i)) (just (o' , i')) = just (o ∪ₒ o' , i ∪ᵢ i')

imap (i ∪ᵢ i') op = (imap i op) ∪-aux (imap i' op)


-- SETTING THE VALUE OF EFFECT ANNOTATION AT A SPECIFIC INTERRUPT NAME

_[_↦_]ᵢ : I → Σₛ → Maybe (O × I) → I
imap (i [ op ↦ v ]ᵢ) op' = if op ≡ op' then v else imap i op'


-- ACTION OF INTERRUPTS ON EFFECT ANNOTATIONS

infix 40 _↓ₑ_

↓ₑ-auxₒ : Σₛ → Maybe (O × I) → O → O
↓ₑ-auxₒ op nothing o = o
↓ₑ-auxₒ op (just (o' , i')) o = o ∪ₒ o'

↓ₑ-auxᵢ : Σₛ → Maybe (O × I) → I → I
↓ₑ-auxᵢ op nothing i = i
↓ₑ-auxᵢ op (just (o' , i')) i = (i [ op ↦ nothing ]ᵢ) ∪ᵢ i'

_↓ₑ_ : Σₛ → O × I → O × I
op ↓ₑ (o , i) =
  ↓ₑ-auxₒ op (imap i op) o , ↓ₑ-auxᵢ op (imap i op) i


-- GENERALISED ACTION OF INTERRUPTS ON EFFECT ANNOTATIONS

_↓↓ₑ_ : List Σₛ → O × I → O × I
[] ↓↓ₑ (o , i) = o , i
(op ∷ ops) ↓↓ₑ (o , i) = op ↓ₑ (ops ↓↓ₑ (o , i))

↓↓ₑ-act : (ops ops' : List Σₛ) → 
          ------------------------------------------------------
          (ops ++ ops') ↓↓ₑ (o , i) ≡ ops ↓↓ₑ (ops' ↓↓ₑ (o , i))
↓↓ₑ-act [] ops' =
  refl
↓↓ₑ-act (op ∷ ops) ops' =
  cong (λ oi → op ↓ₑ oi) (↓↓ₑ-act ops ops')


-- CHECKING THE CONTENTS OF EFFECT ANNOTATIONS

_∈ₒ_ : Σₛ → O → Set
op ∈ₒ (omap o) = o op ≡ just tt

lkpᵢ : Σₛ → I → Maybe (O × I)
lkpᵢ op i = imap i op


-- SUBTYPING RELATIONS FOR EFFECT ANNOTATIONS

_⊑ₒ_ : O → O → Set
o ⊑ₒ o' = (op : Σₛ) → op ∈ₒ o → op ∈ₒ o'

record _⊑ᵢ_ (i i' : I) : Set

_⊑-aux_ : Maybe (O × I) → Maybe (O × I) → Set
nothing ⊑-aux _ = ⊤
just _ ⊑-aux nothing = ⊥
just (o , i) ⊑-aux just (o' , i') = o ⊑ₒ o' × i ⊑ᵢ i'

record _⊑ᵢ_ i i' where
  coinductive
  field
    rel : ∀ op → (imap i op) ⊑-aux (imap i' op)
        
open _⊑ᵢ_ public

_⊑_ : O × I → O × I → Set
(o , i) ⊑ (o' , i') = o ⊑ₒ o' × i ⊑ᵢ i'

-- SUBTYPING RELATIONS ARE PREORDERS

⊑ₒ-refl : o ⊑ₒ o
⊑ₒ-refl = λ op p → p

⊑ₒ-trans : o ⊑ₒ o' → o' ⊑ₒ o'' → o ⊑ₒ o''
⊑ₒ-trans p q = λ op r → q op (p op r)

⊑ᵢ-refl : i ⊑ᵢ i

⊑-aux-refl : ∀ m → m ⊑-aux m
⊑-aux-refl (just (fst , snd)) = ⊑ₒ-refl , ⊑ᵢ-refl
⊑-aux-refl nothing = tt

rel ⊑ᵢ-refl op = ⊑-aux-refl _

⊑ᵢ-trans : i ⊑ᵢ i' → i' ⊑ᵢ i'' → i ⊑ᵢ i''

⊑-aux-trans : ∀ m m' m'' → m ⊑-aux m' → m' ⊑-aux m'' → m ⊑-aux m''
⊑-aux-trans (just (o , i)) (just (o' , i')) (just (o'' , i'')) (o⊑o' , i⊑i') (o'⊑o'' , i'⊑i'') =
  ⊑ₒ-trans o⊑o' o'⊑o'' , ⊑ᵢ-trans i⊑i' i'⊑i''
⊑-aux-trans nothing _ _ _ _ =
  tt

rel (⊑ᵢ-trans p q) op = ⊑-aux-trans _ _ _ (rel p op) (rel q op)


-- SUBTYPING RELATIONS ARE PROOF-IRRELEVANT

≡-uip : {A : Set} {a b : A} (p q : a ≡ b) → p ≡ q
≡-uip refl refl = refl

⊑ₒ-irrelevant : (p q : o ⊑ₒ o') → p ≡ q
⊑ₒ-irrelevant {omap o} {omap o'} p q =
  fun-ext (λ op → fun-ext (λ r → ≡-uip _ _))

  
-- LEFT AND RIGHT INCLUSIONS INTO UNIONS OF EFFECT ANNOTATIONS

∪ₒ-inl : o ⊑ₒ (o ∪ₒ o')
∪ₒ-inl {omap o} {omap o'} op with o op | o' op
... | nothing | nothing = λ p → p
... | nothing | just tt = λ _ → refl
... | just tt | nothing = λ p → p
... | just tt | just tt = λ p → p

∪ₒ-inr : o' ⊑ₒ (o ∪ₒ o')
∪ₒ-inr {omap o} {omap o'} op with o op | o' op
... | nothing | nothing = λ p → p
... | nothing | just tt = λ _ → refl
... | just tt | nothing = λ _ → refl
... | just tt | just tt = λ p → p


∪ᵢ-inl : i ⊑ᵢ (i ∪ᵢ i')

∪-aux-inl : ∀ m m' → m ⊑-aux (m ∪-aux m')
∪-aux-inl (just (o , i)) (just (o' , i')) = ∪ₒ-inl , ∪ᵢ-inl
∪-aux-inl (just (_ , _)) nothing = ⊑ₒ-refl , ⊑ᵢ-refl
∪-aux-inl nothing _ = tt

rel ∪ᵢ-inl op = ∪-aux-inl _ _

∪ᵢ-inr : i' ⊑ᵢ (i ∪ᵢ i')

∪-aux-inr : ∀ m m' → m' ⊑-aux (m ∪-aux m')
∪-aux-inr (just (o , i)) (just (o' , i')) = ∪ₒ-inr , ∪ᵢ-inr
∪-aux-inr nothing (just (_ , _)) = ⊑ₒ-refl , ⊑ᵢ-refl
∪-aux-inr _ nothing = tt

rel ∪ᵢ-inr op = ∪-aux-inr _ _

∪ₒ-copair : o ⊑ₒ o'' → o' ⊑ₒ o'' → (o ∪ₒ o') ⊑ₒ o''
∪ₒ-copair {o = omap o} {o' = omap o'} p q op with o op | o' op | p op | q op
... | just tt | just tt | f | g = f
... | just tt | nothing | f | g = f
... | nothing |       _ | f | g = g

∪ᵢ-copair : i ⊑ᵢ i'' → i' ⊑ᵢ i'' → (i ∪ᵢ i') ⊑ᵢ i''

∪-aux-copair : ∀ m m' m'' → m ⊑-aux m'' → m' ⊑-aux m'' → (m ∪-aux m') ⊑-aux m''
∪-aux-copair (just (o , i)) (just (o' , i')) (just (o'' , i'')) (p , q) (s , t) = ∪ₒ-copair p s , ∪ᵢ-copair q t
∪-aux-copair (just _) (just _) nothing ()
∪-aux-copair (just _) nothing _ p q = p
∪-aux-copair nothing _ _ p q = q

rel (∪ᵢ-copair p q) op = ∪-aux-copair _ _ _ (rel p op) (rel q op)


-- FUNCTORIALITY OF UNIONS OF EFFECT ANNOTATIONS

∪ₒ-fun : o ⊑ₒ o'' → o' ⊑ₒ o''' → (o ∪ₒ o') ⊑ₒ (o'' ∪ₒ o''')
∪ₒ-fun p q = ∪ₒ-copair (⊑ₒ-trans p ∪ₒ-inl) (⊑ₒ-trans q ∪ₒ-inr)

∪ᵢ-fun : i ⊑ᵢ i'' → i' ⊑ᵢ i''' → (i ∪ᵢ i') ⊑ᵢ (i'' ∪ᵢ i''')
∪ᵢ-fun p q = ∪ᵢ-copair (⊑ᵢ-trans p ∪ᵢ-inl) (⊑ᵢ-trans q ∪ᵢ-inr)


-- INCLUSION INTO ACTED UPON EFFECT ANNOTATION

{- LEMMA 3.1 (1) -}

↓ₑ-⊑ₒ : o ⊑ₒ pr₁ (op ↓ₑ (o , i))
↓ₑ-⊑ₒ {omap o} {op} {i} op' p with imap i op
... | nothing = p
... | just (o' , i') = ∪ₒ-inl op' p


{- LEMMA 3.1 (2) - the O part -}

inj-just : {A : Set} {a b : A} → just a ≡ just b → a ≡ b
inj-just refl = refl

inj-pair₁ : {A B : Set} {a b : A} {a' b' : B} → (a , a') ≡ (b , b') → a ≡ b
inj-pair₁ refl = refl

inj-pair₂ : {A B : Set} {a b : A} {a' b' : B} → (a , a') ≡ (b , b') → a' ≡ b'
inj-pair₂ refl = refl

↓ₑ-⊑ₒ-o' : imap i op ≡ just (o' , i') → 
           ---------------------------
           o' ⊑ₒ pr₁ (op ↓ₑ (o , i))
↓ₑ-⊑ₒ-o' {i = i} {op = op} {o = omap o} p with imap i op
... | just (_ , _) rewrite inj-pair₁ (inj-just p) = ∪ₒ-inr


{- LEMMA 3.1 (2) - the I part -}

↓ₑ-⊑ₒ-i' : imap i op ≡ just (o' , i') → 
           ---------------------------
           i' ⊑ᵢ pr₂ (op ↓ₑ (o , i))
↓ₑ-⊑ₒ-i' {i = i} {op = op} {o = omap o} p with imap i op
... | just (_ , _) rewrite inj-pair₂ (inj-just p) = ∪ᵢ-inr


-- EFFECT ANNOTATION OF AN INTERRUPT THAT WAS NOT ACTED WITH

{- LEMMA 3.1 (3) -}

lkpᵢ-↓ₑ-neq-⊑ : ¬ op ≡ op' →
                -------------------------
                imap i op' ⊑-aux imap (pr₂ (op ↓ₑ (o , i))) op'
lkpᵢ-↓ₑ-neq-⊑ {op} {i = i} {o = omap o} p with imap i op
... | nothing = ⊑-aux-refl _
... | just (_ , _) = subst (λ z → _ ⊑-aux (z ∪-aux _)) (sym (ite-≢ p)) (∪-aux-inl _ _)


-- ACTION OF INTERRUPTS ON EFFECT ANNOTATIONS IS MONOTONIC

[↦]ᵢ-monotonic : i ⊑ᵢ i' → (i [ op ↦ nothing ]ᵢ) ⊑ᵢ (i' [ op ↦ nothing ]ᵢ)
rel ([↦]ᵢ-monotonic {op = op} p) op' with decₛ op op'
... | yes _ = tt
... | no  _ = rel p op'

[↦]ᵢ-nothing : imap i op ≡ nothing → i ⊑ᵢ (i [ op ↦ nothing ]ᵢ)
rel ([↦]ᵢ-nothing {op = op} p) op' with decₛ op op'
... | yes refl rewrite p = tt
... | no  _ = ⊑-aux-refl _

↓ₑ-monotonicₒ : o ⊑ₒ o' →
                i ⊑ᵢ i' →
                ------------------------------------------------
                pr₁ (op ↓ₑ (o , i)) ⊑ₒ pr₁ (op ↓ₑ (o' , i'))

↓ₑ-monotonicᵢ : o ⊑ₒ o' →
                i ⊑ᵢ i' →
                ------------------------------------------------
                pr₂ (op ↓ₑ (o , i)) ⊑ᵢ pr₂ (op ↓ₑ (o' , i'))

↓ₑ-monotonicₒ {omap o} {omap o'} {i} {i'} {op} p q with imap i op | imap i' op | rel q op
... | just (_ , _) | just (_ , _) | f = ∪ₒ-fun p (pr₁ f)
... | nothing      | just _       | _ = ⊑ₒ-trans p ∪ₒ-inl
... | nothing      | nothing      | _ = p

↓ₑ-monotonicᵢ {omap o} {omap o'} {i} {i'} {op} p q with imap i op in eq | imap i' op | rel q op
... | just (_ , _) | just (_ , _) | f = ∪ᵢ-fun ([↦]ᵢ-monotonic q) (pr₂ f)
... | nothing      | just (_ , _) | f = ⊑ᵢ-trans ([↦]ᵢ-nothing eq) (⊑ᵢ-trans ([↦]ᵢ-monotonic q) ∪ᵢ-inl)
... | nothing      | nothing      | f = q


-- GENERALISED ACTION OF INTERRUPTS ON EFFECT ANNOTATIONS IS MONOTONIC

↓↓ₑ-monotonicₒ : (ops : List Σₛ) →
                 o ⊑ₒ o' →
                 i ⊑ᵢ i' →
                 ----------------------------------------------------
                 pr₁ (ops ↓↓ₑ (o , i)) ⊑ₒ pr₁ (ops ↓↓ₑ (o' , i'))

↓↓ₑ-monotonicᵢ : (ops : List Σₛ) →
                 o ⊑ₒ o' →
                 i ⊑ᵢ i' →
                 ----------------------------------------------------
                 pr₂ (ops ↓↓ₑ (o , i)) ⊑ᵢ pr₂ (ops ↓↓ₑ (o' , i'))

↓↓ₑ-monotonicₒ {omap o} {omap o'} {i} {i'} [] p q =
  p
↓↓ₑ-monotonicₒ (op ∷ ops) p q =
  ↓ₑ-monotonicₒ (↓↓ₑ-monotonicₒ ops p q) (↓↓ₑ-monotonicᵢ ops p q)

↓↓ₑ-monotonicᵢ [] p q =
  q
↓↓ₑ-monotonicᵢ (op ∷ ops) p q =
  ↓ₑ-monotonicᵢ (↓↓ₑ-monotonicₒ ops p q) (↓↓ₑ-monotonicᵢ ops p q)


-- INCLUSION INTO GENERALLY ACTED UPON EFFECT ANNOTATION

↓↓ₑ-⊑ₒ : (ops : List Σₛ) →
         --------------------------
         o ⊑ₒ pr₁ (ops ↓↓ₑ (o , i))
↓↓ₑ-⊑ₒ [] = ⊑ₒ-refl
↓↓ₑ-⊑ₒ (op ∷ ops) = ⊑ₒ-trans (↓↓ₑ-⊑ₒ ops) (↓ₑ-⊑ₒ {i = pr₂ (ops ↓↓ₑ _)})


-- A PATH OF INTERRUPT NAMES THAT REVEALS THE GIVEN SIGNAL IN AN EFFECT ANNOTATION

data _`at_`in_ (op : Σₛ) : List Σₛ → O × I → Set where

  stop : op ∈ₒ o →
         -------------------
         op `at [] `in (o , i)
         
  next : imap i op' ≡ just (o' , i') →
         op `at ops `in (o' , i') →
         -----------------------------
         op `at (op' ∷ ops) `in (o , i)


-- A MINIMAL EFFECT ANNOTATION SUCH THAT A GIVEN PATH OF INTERRUPTS REVEALS THE GIVEN SIGNAL NAME

⦃⦃_↦_⦄⦄ₒ : List Σₛ → Σₛ → O

⦃⦃_↦_⦄⦄ᵢ : List Σₛ → Σₛ → I

⦃⦃ [] ↦ op ⦄⦄ₒ = omap (λ op' → if op ≡ op' then just tt else nothing)
⦃⦃ op' ∷ ops ↦ op ⦄⦄ₒ = ∅ₒ

⦃⦃ [] ↦ op ⦄⦄ᵢ = ∅ᵢ
⦃⦃ op' ∷ ops ↦ op ⦄⦄ᵢ = ∅ᵢ [ op' ↦ just (⦃⦃ ops ↦ op ⦄⦄ₒ , ⦃⦃ ops ↦ op ⦄⦄ᵢ) ]ᵢ


-- IF THERE IS A PATH TO A SIGNAL IN AN EFFECT ANNOTATION, THE MINIMAL EFFECT ANNOTATION IS INCLUDED IN IT

`at-minₒ : op `at ops `in (o , i) →
           ----------------------
           ⦃⦃ ops ↦ op ⦄⦄ₒ ⊑ₒ o

`at-minᵢ : op `at ops `in (o , i) →
           ----------------------
           ⦃⦃ ops ↦ op ⦄⦄ᵢ ⊑ᵢ i

`at-minₒ {op} (stop p) op' with decₛ op op'
... | yes refl = λ _ → p
... | no     _ = λ ()
`at-minₒ (next _ _) _ = λ ()

rel (`at-minᵢ (stop x)) op' = tt
rel (`at-minᵢ {ops = op' ∷ _} {i = i} (next x p)) op'' with imap i op' in eq | decₛ op' op''
... | just _ | yes refl rewrite eq | inj-just x = `at-minₒ p , `at-minᵢ p
... |      _ | no     _  = tt

-- SUBPATHS OF (INTERRUPT) NAMES

data _⊆_ : List Σₛ → List Σₛ → Set where

  []  : ----------------
        [] ⊆ ops'
        
  ∷-≡ : ops ⊆ ops' →
        ------------------------
        (op ∷ ops) ⊆ (op ∷ ops')

  ∷-≢ : op ≢ op' →
        (op ∷ ops) ⊆ ops' →
        -------------------------
        (op ∷ ops) ⊆ (op' ∷ ops')

∷-≢-swap : op ≢ op' →
           (op ∷ ops) ⊆ (op' ∷ op ∷ ops') →
           --------------------------------
           (op ∷ ops) ⊆ (op ∷ op' ∷ ops')

∷-∷ : ops ⊆ ops' →
      -------------------
      ops ⊆ (op' ∷ ops')

∷-≢-swap p (∷-≡ q) = ∷-≡ q
∷-≢-swap p (∷-≢ q (∷-≡ r)) = ∷-≡ (∷-∷ r)
∷-≢-swap p (∷-≢ q (∷-≢ r s)) = ⊥-elim (r refl)

∷-∷ [] = []
∷-∷ {op' = op'} (∷-≡ {op = op} p) with decₛ op op'
... | yes refl = ∷-≡ (∷-∷ p)
... | no ¬q = ∷-≢ ¬q (∷-≡ p)
∷-∷ {op' = op'} (∷-≢ {op = op} p q) with decₛ op op'
... | yes refl = ∷-≢-swap p (∷-≢ p (∷-∷ q))
... | no ¬r = ∷-≢ ¬r (∷-≢ p q)


-- IF A SUBPATH OF INTERRUPTS REVEALS A SIGNAL, THEN ACTING WITH THE WHOLE PATH ALSO REVEALS IT
           
⊆-↓↓ : ops ⊆ ops' →
       ---------------------------------------------------------------
       op ∈ₒ pr₁ (reverse ops' ↓↓ₑ (⦃⦃ ops ↦ op ⦄⦄ₒ , ⦃⦃ ops ↦ op ⦄⦄ᵢ))
⊆-↓↓ {ops' = ops'} {op = op} [] = (↓↓ₑ-⊑ₒ (reverse ops')) op ite-≡
⊆-↓↓ {ops = ops} {op = op} (∷-≡ {ops = ops''} {ops' = ops'} {op = op'} p)
  rewrite
  unfold-reverse op' ops' |
  ↓↓ₑ-act {o = ∅ₒ} {i = ∅ᵢ [ op' ↦ just (⦃⦃ ops'' ↦ op ⦄⦄ₒ , ⦃⦃ ops'' ↦ op ⦄⦄ᵢ) ]ᵢ} (reverse ops') [ op' ] |
  ite-≡ {op = op'} {x = just (⦃⦃ ops'' ↦ op ⦄⦄ₒ , ⦃⦃ ops'' ↦ op ⦄⦄ᵢ)} {y = nothing} =
  ↓↓ₑ-monotonicₒ (reverse ops') ∪ₒ-inr ∪ᵢ-inr op (⊆-↓↓ p)
⊆-↓↓ {ops = ops} {op = op} (∷-≢ {op = op''} {op' = op'} {ops = ops'} {ops' = ops''} x p)
  rewrite
  unfold-reverse op' ops'' |
  ↓↓ₑ-act {o = ∅ₒ} {i = ∅ᵢ [ op'' ↦ just (⦃⦃ ops' ↦ op ⦄⦄ₒ , ⦃⦃ ops' ↦ op ⦄⦄ᵢ) ]ᵢ} (reverse ops'') [ op' ] |
  ite-≢ {x = just (⦃⦃ ops' ↦ op ⦄⦄ₒ , ⦃⦃ ops' ↦ op ⦄⦄ᵢ)} {y = nothing} x =
  ↓↓ₑ-monotonicₒ (reverse ops'') (λ _ ()) ⊑ᵢ-refl op (⊆-↓↓ p)

`at-⊎ : op `at ops `in (o ∪ₒ o' , i ∪ᵢ i') →
        -------------------------------------------------
        (op `at ops `in (o , i)) ⊎ (op `at ops `in (o' , i'))
`at-⊎ {op = op} {o = omap o} {o' = omap o'} (stop x) with o op in eq | o' op in eq'
... | just tt | just tt = inj₁ (stop eq)
... | just tt | nothing = inj₁ (stop eq)
... | nothing | just tt = inj₂ (stop eq')
`at-⊎ {i = i} {i' = i'} (next {op' = op'} x p) with imap i op' in eq | imap i' op' in eq'
... | just (_ , _) | nothing      rewrite inj-just x = inj₁ (next eq p)
... | nothing      | just (_ , _) rewrite inj-just x = inj₂ (next eq' p)
... | just (_ , _) | just (_ , _) rewrite sym (inj-just x) with `at-⊎ p
...   | inj₁ p = inj₁ (next eq p)
...   | inj₂ p = inj₂ (next eq' p)

↓↓-⊆-rw : reverse (op ∷ ops) ↓↓ₑ (o , i) ≡ reverse ops ↓↓ₑ (op ↓ₑ (o , i))
↓↓-⊆-rw {op} {ops} {o} {i} =
  trans (cong (λ ops' → ops' ↓↓ₑ (o , i)) (unfold-reverse op ops)) (↓↓ₑ-act (reverse ops) [ op ])

↓↓-⊆-aux-aux : (ops' : List Σₛ) →
               ops' ⊆ ops →
               (op `at ops' `in (o , (i [ op' ↦ nothing ]ᵢ))) →
               -------------------------------------------------------------------------------
               Σ[ ops'' ∈ List Σₛ ] (ops'' ⊆ (op' ∷ ops) × (op `at ops'' `in (o , i)))
↓↓-⊆-aux-aux [] r (stop t) =
  [] , [] , stop t
↓↓-⊆-aux-aux {op' = op'} (op'' ∷ ops'') r (next t u) with decₛ op' op''
... | no ¬v =
  op'' ∷ ops'' , ∷-≢ (λ w → ¬v (sym w)) r , next t u

↓↓-⊆ : (ops : List Σₛ) → 
       op ∈ₒ pr₁ (reverse ops ↓↓ₑ (o , i)) → 
       ----------------------------------------------------------
       Σ[ ops' ∈ List Σₛ ] (ops' ⊆ ops × (op `at ops' `in (o , i)))
↓↓-⊆ [] p =
  [] , [] , stop p
↓↓-⊆ {op} {omap o} {i} (op' ∷ ops) p
  rewrite ↓↓-⊆-rw {op'} {ops} {omap o} {i} with imap i op' in eq | ↓↓-⊆ ops p
... | nothing | ops' , r , s = ops' , ∷-∷ r , s
... | just (_ , _) | ops' , r , s with `at-⊎ s
...   | inj₁ x = ↓↓-⊆-aux-aux ops' r x
...   | inj₂ y = op' ∷ ops' , ∷-≡ r , next eq y


-- ENVELOPING THE EFFECT ANNOTATION REDUCTION WITH MLTIPLE INTERRUPT ACTIONS

{- LEMMA 4.5 -}

↓↓ₑ-⊑ₒ-act : (ops : List Σₛ) →
             (op : Σₛ) →
             ----------------------------------------------------------
             pr₁ (ops ↓↓ₑ (o , i)) ⊑ₒ pr₁ (ops ↓↓ₑ (op ↓ₑ (o , i)))
↓↓ₑ-⊑ₒ-act {o} {i} ops op op' p rewrite sym (reverse-involutive ops) with ↓↓-⊆ (reverse ops) p
... | ops' , q , r with ↓↓ₑ-monotonicₒ (reverse (op ∷ reverse ops)) (`at-minₒ r) (`at-minᵢ r) op' (⊆-↓↓ (∷-∷ q))
...   | t rewrite ↓↓-⊆-rw {op} {reverse ops} {o} {i} | reverse-involutive ops = t

o⊑ : just (o' , i') ⊑-aux imap i op → o' ⊑ₒ pr₁ (op ↓ₑ (o , i))
o⊑ {i = i} {op = op} p with imap i op
... | just (_ , _) = ⊑ₒ-trans (pr₁ p) ∪ₒ-inr

i⊑ : just (o' , i') ⊑-aux imap i op → i' ⊑ᵢ pr₂ (op ↓ₑ (o , i))
i⊑ {i = i} {op = op} p with imap i op
... | just (_ , _) = ⊑ᵢ-trans (pr₂ p) ∪ᵢ-inr