open import Data.Nat using (ℕ; suc; _+_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; +-assoc; +-comm; +-monoʳ-<; +-monoˡ-<; ≤-refl)
open import Data.Nat.Induction renaming (<-wellFounded to <-wf)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module AEffFinTreeSN.ParallelShape where

-- LEXICOGRAPHIC ORDERING ON PAIRS OF NATURAL NUMBERS AND PROOF THAT IT IS WELL FOUNDED

_<ₗₑₓ_ : ℕ × ℕ → ℕ × ℕ → Set
(n , m) <ₗₑₓ (k , l) = n < k ⊎ n ≡ k × m < l

<ₗₑₓ-wf' : {n m : ℕ} →
           Acc _<_ n →
           Acc _<_ m →
           --------------------------------------------
           {k : ℕ × ℕ} → k <ₗₑₓ (n , m) → Acc _<ₗₑₓ_ k

<ₗₑₓ-wf' (acc an) _ (inj₁ x) = acc (<ₗₑₓ-wf' (an x) (<-wf _))
<ₗₑₓ-wf' an (acc am) (inj₂ (refl , x)) = acc (<ₗₑₓ-wf' an (am x))

<ₗₑₓ-wf : (p : ℕ × ℕ) → Acc _<ₗₑₓ_ p
<ₗₑₓ-wf (n , m) = acc (<ₗₑₓ-wf' (<-wf _) (<-wf _))


-- DATATYPE ENCODING THE ABSTRACT SHAPE OF THE PARALLEL PART OF A TERM

data ParallelShape : Set where
  run : ParallelShape
  _∥_ : ParallelShape → ParallelShape → ParallelShape
  ↓   : ParallelShape → ParallelShape
  ↑   : ParallelShape → ParallelShape

variable
  Ps Ps' Qs Qs' Rs Rs' : ParallelShape


-- REDUCTION OF PARALLEL SHAPES

infix 4 _⇝_
data _⇝_ : ParallelShape → ParallelShape → Set where
  ↑-∥ₗ       : ↑ Ps ∥ Qs ⇝ ↑ (Ps ∥ ↓ Qs)
  ↑-∥ᵣ       : Ps ∥ ↑ Qs ⇝ ↑ (↓ Ps ∥ Qs)
  ↓-run      : ↓ run ⇝ run
  ↓-∥        : ↓ (Ps ∥ Qs) ⇝ ↓ Ps ∥ ↓ Qs
  ↓-↑        : ↓ (↑ Ps) ⇝ ↑ (↓ Ps)
  context-∥ₗ : Ps ⇝ Ps' → Ps ∥ Qs ⇝ Ps' ∥ Qs
  context-∥ᵣ : Qs ⇝ Qs' → Ps ∥ Qs ⇝ Ps ∥ Qs'
  context-↑  : Ps ⇝ Ps' → ↑ Ps ⇝ ↑ Ps'
  context-↓  : Ps ⇝ Ps' → ↓ Ps ⇝ ↓ Ps'


private

  -- NUMBER OF SIGNALS IN A PARALLEL SHAPE

  #↑ₛ : ParallelShape → ℕ
  #↑ₛ run = 0
  #↑ₛ (Ps ∥ Qs) = #↑ₛ Ps + #↑ₛ Qs
  #↑ₛ (↓ Ps) = #↑ₛ Ps
  #↑ₛ (↑ Ps) = suc (#↑ₛ Ps)


  -- NUMBER OF NODES OF A PARALLEL SHAPE REGARDED AS A BINARY TREE

  size : ParallelShape → ℕ
  size run = 1
  size (Ps ∥ Qs) = suc (size Ps + size Qs)
  size (↓ Ps) = size Ps
  size (↑ Ps) = size Ps


  -- NUMBER OF REMAINING ↓-run, ↓-∥ AND ↓-↑ REDUCTIONS ASSUMING NO ↑-∥ₗ OR ↑-∥ᵣ REDUCTION HAPPENS

  ∣_∣↓ : ParallelShape → ℕ
  ∣ run ∣↓ = 0
  ∣ Ps ∥ Qs ∣↓ = ∣ Ps ∣↓ + ∣ Qs ∣↓
  ∣ ↓ Ps ∣↓ = ∣ Ps ∣↓ + (size Ps + #↑ₛ Ps)
  ∣ ↑ Ps ∣↓ = ∣ Ps ∣↓


  -- NUMBER OF REMAINING ↑-∥ₗ AND ↑-∥ᵣ REDUCTIONS

  ∣_∣↑ : ParallelShape → ℕ
  ∣ run ∣↑ = 0
  ∣ Ps ∥ Qs ∣↑ = (∣ Ps ∣↑ + #↑ₛ Ps) + (∣ Qs ∣↑ + #↑ₛ Qs)
  ∣ ↓ Ps ∣↑ = ∣ Ps ∣↑
  ∣ ↑ Ps ∣↑ = ∣ Ps ∣↑


  -- REDUCTION PRESERVES NUMBER OF SIGNALS AND SIZE

  #↑ₛ-⇝-≡ : Ps ⇝ Qs → #↑ₛ Qs ≡ #↑ₛ Ps
  #↑ₛ-⇝-≡ ↑-∥ₗ = refl
  #↑ₛ-⇝-≡ ↑-∥ᵣ = sym (+-suc _ _)
  #↑ₛ-⇝-≡ ↓-run = refl
  #↑ₛ-⇝-≡ ↓-∥ = refl
  #↑ₛ-⇝-≡ ↓-↑ = refl
  #↑ₛ-⇝-≡ (context-∥ₗ r) rewrite #↑ₛ-⇝-≡ r = refl
  #↑ₛ-⇝-≡ (context-∥ᵣ r) rewrite #↑ₛ-⇝-≡ r = refl
  #↑ₛ-⇝-≡ (context-↑ r) rewrite #↑ₛ-⇝-≡ r = refl
  #↑ₛ-⇝-≡ (context-↓ r) rewrite #↑ₛ-⇝-≡ r = refl

  size-⇝-≡ : Ps ⇝ Qs → size Qs ≡ size Ps
  size-⇝-≡ ↑-∥ₗ = refl
  size-⇝-≡ ↑-∥ᵣ = refl
  size-⇝-≡ ↓-run = refl
  size-⇝-≡ ↓-∥ = refl
  size-⇝-≡ ↓-↑ = refl
  size-⇝-≡ (context-∥ₗ r) rewrite size-⇝-≡ r = refl
  size-⇝-≡ (context-∥ᵣ r) rewrite size-⇝-≡ r = refl
  size-⇝-≡ (context-↑ r) rewrite size-⇝-≡ r = refl
  size-⇝-≡ (context-↓ r) rewrite size-⇝-≡ r = refl


  -- ARITHMETIC LEMMAS

  +-lemma-≡ : (i j k l m n : ℕ) → i + (j + k) + (l + (m + n)) ≡ i + l + (j + m + (k + n))
  +-lemma-≡ i j k l m n
    rewrite
    +-assoc i (j + k) (l + (m + n)) |
    sym (+-assoc l m n) |
    sym (+-assoc (j + k) (l + m) n) |
    sym (+-assoc (j + k) l m) |
    +-comm (j + k) l |
    +-assoc l (j + k) m |
    +-assoc j k m |
    +-comm k m |
    +-assoc l (j + (m + k)) n |
    sym (+-assoc i l (j + (m + k) + n)) |
    sym (+-assoc j m k) |
    +-assoc (j + m) k n =
    refl

  +-lemma-< : (i j k l m n : ℕ) → i + (j + k) + (l + (m + n)) < i + l + suc (j + m + (k + n))
  +-lemma-< i j k l m n rewrite +-lemma-≡ i j k l m n = +-monoʳ-< _ ≤-refl


-- PARALLEL SHAPE REDUCTION EITHER DECREASES ∣_∣↑ OR LEAVES ∣_∣↑ UNCHANGED AND DECREASES ∣_∣↓

∣_∣p : ParallelShape → ℕ × ℕ
∣ Ps ∣p = ∣ Ps ∣↑ , ∣ Ps ∣↓

maxs-< : Ps ⇝ Qs → ∣ Qs ∣p <ₗₑₓ ∣ Ps ∣p
maxs-< {Ps = ↑ Ps ∥ _} ↑-∥ₗ =
  inj₁ (+-monoˡ-< _ (+-monoʳ-< ∣ Ps ∣↑ ≤-refl))
maxs-< {Ps = Ps ∥ _} ↑-∥ᵣ =
  inj₁ (+-monoʳ-< (∣ Ps ∣↑ + #↑ₛ Ps) (+-monoʳ-< _ ≤-refl))
maxs-< ↓-run =
  inj₂ (refl , s≤s z≤n)
maxs-< {Ps = ↓ (Ps ∥ _)} ↓-∥ =
  inj₂ (refl , +-lemma-< ∣ Ps ∣↓ _ (#↑ₛ Ps) _ _ _)
maxs-< {Ps = ↓ (↑ Ps)} ↓-↑ =
  inj₂ (refl , +-monoʳ-< ∣ Ps ∣↓ (+-monoʳ-< _ ≤-refl))
maxs-< (context-∥ₗ r) rewrite #↑ₛ-⇝-≡ r with maxs-< r
... | inj₁ x = inj₁ (+-monoˡ-< _ (+-monoˡ-< _ x))
... | inj₂ (x , y) rewrite x = inj₂ (refl , +-monoˡ-< _ y)
maxs-< {Ps = Ps ∥ _} (context-∥ᵣ r) rewrite #↑ₛ-⇝-≡ r with maxs-< r
... | inj₁ x = inj₁ (+-monoʳ-< (∣ Ps ∣↑ + #↑ₛ Ps) (+-monoˡ-< _ x))
... | inj₂ (x , y) rewrite x = inj₂ (refl , +-monoʳ-< _ y)
maxs-< (context-↑ r) =
  maxs-< r
maxs-< (context-↓ r) rewrite #↑ₛ-⇝-≡ r | size-⇝-≡ r with maxs-< r
... | inj₁ x = inj₁ x
... | inj₂ (x , y) = inj₂ (x , +-monoˡ-< _ y)