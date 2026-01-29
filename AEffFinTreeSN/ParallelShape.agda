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
  S S' T T' : ParallelShape


-- REDUCTION OF PARALLEL SHAPES

infix 4 _⇝_
data _⇝_ : ParallelShape → ParallelShape → Set where
  ↑-∥ₗ       : ↑ S ∥ T ⇝ ↑ (S ∥ ↓ T)
  ↑-∥ᵣ       : S ∥ ↑ T ⇝ ↑ (↓ S ∥ T)
  ↓-run      : ↓ run ⇝ run
  ↓-∥        : ↓ (S ∥ T) ⇝ ↓ S ∥ ↓ T
  ↓-↑        : ↓ (↑ S) ⇝ ↑ (↓ S)
  context-∥ₗ : S ⇝ S' → S ∥ T ⇝ S' ∥ T
  context-∥ᵣ : T ⇝ T' → S ∥ T ⇝ S ∥ T'
  context-↑  : S ⇝ S' → ↑ S ⇝ ↑ S'
  context-↓  : S ⇝ S' → ↓ S ⇝ ↓ S'


private

  -- NUMBER OF SIGNALS IN A PARALLEL SHAPE

  #↑ₛ : ParallelShape → ℕ
  #↑ₛ run = 0
  #↑ₛ (S ∥ T) = #↑ₛ S + #↑ₛ T
  #↑ₛ (↓ S) = #↑ₛ S
  #↑ₛ (↑ S) = suc (#↑ₛ S)


  -- NUMBER OF NODES OF A PARALLEL SHAPE REGARDED AS A BINARY TREE

  size : ParallelShape → ℕ
  size run = 1
  size (S ∥ T) = suc (size S + size T)
  size (↓ S) = size S
  size (↑ S) = size S


  -- NUMBER OF REMAINING ↓-run, ↓-∥ AND ↓-↑ REDUCTIONS ASSUMING NO ↑-∥ₗ OR ↑-∥ᵣ REDUCTION HAPPENS

  ∣_∣↓ : ParallelShape → ℕ
  ∣ run ∣↓ = 0
  ∣ S ∥ T ∣↓ = ∣ S ∣↓ + ∣ T ∣↓
  ∣ ↓ S ∣↓ = ∣ S ∣↓ + (size S + #↑ₛ S)
  ∣ ↑ S ∣↓ = ∣ S ∣↓


  -- NUMBER OF REMAINING ↑-∥ₗ AND ↑-∥ᵣ REDUCTIONS

  ∣_∣↑ : ParallelShape → ℕ
  ∣ run ∣↑ = 0
  ∣ S ∥ T ∣↑ = (∣ S ∣↑ + #↑ₛ S) + (∣ T ∣↑ + #↑ₛ T)
  ∣ ↓ S ∣↑ = ∣ S ∣↑
  ∣ ↑ S ∣↑ = ∣ S ∣↑


  -- REDUCTION PRESERVES NUMBER OF SIGNALS AND SIZE

  #↑ₛ-⇝-≡ : S ⇝ T → #↑ₛ T ≡ #↑ₛ S
  #↑ₛ-⇝-≡ ↑-∥ₗ = refl
  #↑ₛ-⇝-≡ ↑-∥ᵣ = sym (+-suc _ _)
  #↑ₛ-⇝-≡ ↓-run = refl
  #↑ₛ-⇝-≡ ↓-∥ = refl
  #↑ₛ-⇝-≡ ↓-↑ = refl
  #↑ₛ-⇝-≡ (context-∥ₗ r) rewrite #↑ₛ-⇝-≡ r = refl
  #↑ₛ-⇝-≡ (context-∥ᵣ r) rewrite #↑ₛ-⇝-≡ r = refl
  #↑ₛ-⇝-≡ (context-↑ r) rewrite #↑ₛ-⇝-≡ r = refl
  #↑ₛ-⇝-≡ (context-↓ r) rewrite #↑ₛ-⇝-≡ r = refl

  size-⇝-≡ : S ⇝ T → size T ≡ size S
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
∣ S ∣p = ∣ S ∣↑ , ∣ S ∣↓

maxs-< : S ⇝ T → ∣ T ∣p <ₗₑₓ ∣ S ∣p
maxs-< {S = ↑ S ∥ _} ↑-∥ₗ =
  inj₁ (+-monoˡ-< _ (+-monoʳ-< ∣ S ∣↑ ≤-refl))
maxs-< {S = S ∥ _} ↑-∥ᵣ =
  inj₁ (+-monoʳ-< (∣ S ∣↑ + #↑ₛ S) (+-monoʳ-< _ ≤-refl))
maxs-< ↓-run =
  inj₂ (refl , s≤s z≤n)
maxs-< {S = ↓ (S ∥ _)} ↓-∥ =
  inj₂ (refl , +-lemma-< ∣ S ∣↓ _ (#↑ₛ S) _ _ _)
maxs-< {S = ↓ (↑ S)} ↓-↑ =
  inj₂ (refl , +-monoʳ-< ∣ S ∣↓ (+-monoʳ-< _ ≤-refl))
maxs-< (context-∥ₗ r) rewrite #↑ₛ-⇝-≡ r with maxs-< r
... | inj₁ x = inj₁ (+-monoˡ-< _ (+-monoˡ-< _ x))
... | inj₂ (x , y) rewrite x = inj₂ (refl , +-monoˡ-< _ y)
maxs-< {S = S ∥ _} (context-∥ᵣ r) rewrite #↑ₛ-⇝-≡ r with maxs-< r
... | inj₁ x = inj₁ (+-monoʳ-< (∣ S ∣↑ + #↑ₛ S) (+-monoˡ-< _ x))
... | inj₂ (x , y) rewrite x = inj₂ (refl , +-monoʳ-< _ y)
maxs-< (context-↑ r) =
  maxs-< r
maxs-< (context-↓ r) rewrite #↑ₛ-⇝-≡ r | size-⇝-≡ r with maxs-< r
... | inj₁ x = inj₁ x
... | inj₂ (x , y) = inj₂ (x , +-monoˡ-< _ y)