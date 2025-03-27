open import AEff
open import Types
open import Finality
open import Preservation
open import Renamings
open import Substitutions

open import SubstitutionProperties

open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; s≤s; _+_)
open import Data.Nat.Properties using (+-monoˡ-≤; +-monoʳ-≤; m≤m⊔n; m≤n⇒m≤o⊔n)
open import Data.Product
open import Data.Empty
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; fromℕ; inject≤) renaming (_+_ to _+F_; suc to sucF)
open import Data.Fin.Patterns
open import Data.Fin.Properties using (inject≤-injective)
open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List renaming (_∷_ to _∷ₗ_; map to mapₗ)

-- standard definition of strong normalization

data SN : {Γ : Ctx} {X : Type} → Γ ⊢M⦂ X → Set where
  sn : {Γ : Ctx}
       {X : Type}
       {M : Γ ⊢M⦂ X} →
       ({N : Γ ⊢M⦂ X} → M ↝↝ N → SN N) →
       --------------------------------
       SN M

-- alternative definition of strong normalization
-- with an upper bound 'm' on the length of reduction sequences
-- necessary because we do an induction on m in append-promise

data SNi : {Γ : Ctx} {X : Type} → ℕ → Γ ⊢M⦂ X → Set where
  sni : {Γ : Ctx}
        {X : Type}
        {m : ℕ}
        {M : Γ ⊢M⦂ X} →
        ({N : Γ ⊢M⦂ X} → M ↝↝ N → SNi m N) →
        --------------------------------
        SNi (suc m) M

-- the rest is proof that the two definitions are equivalent

-- one way is easy

sni→sn : {Γ : Ctx}
         {X : Type}
         {m : ℕ}
         {M : Γ ⊢M⦂ X} →
         SNi m M →
         ------------
         SN M
sni→sn (sni f) = sn (λ r → sni→sn (f r))

-- the other way is hard: first we need to enumerate all one-step reductions from a term

add-context-let : {Γ : Ctx}
                  {X Y : Type}
                  {N : Γ ∷ X ⊢M⦂ Y} →
                  {M : Γ ⊢M⦂ X} →
                  List (Σ[ L ∈ Γ ⊢M⦂ X ] M ↝↝ L) →
                  ---------------------------
                  List (Σ[ L ∈ Γ ⊢M⦂ Y ] (let= M `in N) ↝↝ L)
add-context-let xs = mapₗ (λ {(L , r) → (let= L `in _) , context-let r}) xs

add-context-↑ : {Γ : Ctx}
                {X : Type}
                {op : Σₛ}
                {V : Γ ⊢V⦂ ``(payload op)}
                {M : Γ ⊢M⦂ X} →
                List (Σ[ L ∈ Γ ⊢M⦂ X ] M ↝↝ L) →
                ---------------------------
                List (Σ[ L ∈ Γ ⊢M⦂ X ] ↑ op V M ↝↝ L)
add-context-↑ xs = mapₗ (λ {(L , r) → ↑ _ _ L , context-↑ r}) xs

add-context-↓ : {Γ : Ctx}
                {X : Type}
                {op : Σₛ}
                {V : Γ ⊢V⦂ ``(payload op)}
                {M : Γ ⊢M⦂ X} →
                List (Σ[ L ∈ Γ ⊢M⦂ X ] M ↝↝ L) →
                ---------------------------
                List (Σ[ L ∈ Γ ⊢M⦂ X ] ↓ op V M ↝↝ L)
add-context-↓ xs = mapₗ (λ {(L , r) → ↓ _ _ L , context-↓ r}) xs

add-context-promise : {Γ : Ctx}
                      {X Y : Type}
                      {op : Σₛ}
                      {M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩} →
                      {N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y} →
                      List (Σ[ L ∈ Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ] N ↝↝ L) →
                      ---------------------------
                      List (Σ[ L ∈ Γ ⊢M⦂ Y ] promise op ↦ M `in N ↝↝ L)
add-context-promise xs = mapₗ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) xs

all-reductions : {Γ : Ctx}
                 {X : Type} →
                 (M : Γ ⊢M⦂ X) →
                 ---------------
                 List (Σ[ L ∈ Γ ⊢M⦂ X ] M ↝↝ L)
all-reductions (return V) = []
all-reductions (let= return V `in N) = (_ , let-return V N) ∷ₗ []
all-reductions (let= let= M `in N `in L) = add-context-let (all-reductions (let= M `in N))
all-reductions (let= V · W `in N) = add-context-let (all-reductions (V · W))
all-reductions (let= ↑ op V M `in N) = ((_ , let-↑ V M N)) ∷ₗ (add-context-let (all-reductions (↑ op V M)))
all-reductions (let= ↓ op V M `in N) = add-context-let (all-reductions (↓ op V M))
all-reductions (let= promise op ↦ M `in N `in L) = ((_ , let-promise M N L)) ∷ₗ (add-context-let (all-reductions (promise op ↦ M `in N)))
all-reductions (let= await V until N `in L) = add-context-let (all-reductions (await V until N))
all-reductions ((` x) · W) = []
all-reductions (ƛ M · W) = (_ , apply M W) ∷ₗ []
all-reductions (↑ op V M) = add-context-↑ (all-reductions M)
all-reductions (↓ op V (return V')) = (_ , ↓-return V V') ∷ₗ []
all-reductions (↓ op V (let= M `in N)) = add-context-↓ (all-reductions (let= M `in N))
all-reductions (↓ op V (V' · W)) = add-context-↓ (all-reductions (V' · W))
all-reductions (↓ op V (↑ op' V' M)) = (_ , ↓-↑ V V' M) ∷ₗ (add-context-↓ (all-reductions (↑ op' V' M)))
all-reductions (↓ op V (↓ op' V' M)) = add-context-↓ (all-reductions (↓ op' V' M))
all-reductions {Γ} {X} (↓ op V (promise op' ↦ M `in N)) with rec ← all-reductions (promise op' ↦ M `in N) | decₛ op op'
... | yes refl = (_ , ↓-promise-op V M N) ∷ₗ (add-context-↓ rec)
... | no    ¬≡ = ((_ , ↓-promise-op' ¬≡ V M N)) ∷ₗ (add-context-↓ rec)
all-reductions (↓ op V (await V' until M)) = add-context-↓ (all-reductions (await V' until M))
all-reductions (promise op ↦ M `in return V) = []
all-reductions (promise op ↦ M `in (let= N `in L)) = add-context-promise (all-reductions (let= N `in L))
all-reductions (promise op ↦ M `in (V · W)) = add-context-promise (all-reductions (V · W))
all-reductions (promise op ↦ M `in ↑ op' V N) = ((_ , promise-↑ V M N)) ∷ₗ add-context-promise (all-reductions (↑ op' V N))
all-reductions (promise op ↦ M `in ↓ op' V N) = add-context-promise (all-reductions (↓ op' V N))
all-reductions (promise op ↦ M `in (promise op' ↦ N `in L)) = add-context-promise (all-reductions (promise op' ↦ N `in L))
all-reductions (promise op ↦ M `in (await V until N)) = add-context-promise (all-reductions (await V until N))
all-reductions (await ` x until M) = []
all-reductions (await ⟨ V ⟩ until M) = ((_ , await-promise V M)) ∷ₗ []
all-reductions (await ★ until M) = []

-- inclusion relation for general lists

data _∈ₗ_ {A : Set} (x : A) : List A → Set where
  Hd : {xs : List A} → x ∈ₗ (x ∷ₗ xs)
  Tl : {xs : List A} {m : A} → x ∈ₗ xs → x ∈ₗ (m ∷ₗ xs)

f-∈ : {A B : Set}
      {x : A}
      {xs : List A}
      (f : A → B) →
      x ∈ₗ xs →
      --------------------
      (f x) ∈ₗ (mapₗ f xs)
f-∈ f Hd = Hd
f-∈ f (Tl x∈) = Tl (f-∈ f x∈)

-- the all-reductions function indeed enumerates all possible reductions

all-reductions-complete : {Γ : Ctx}
                          {X : Type}
                          {M N : Γ ⊢M⦂ X} →
                          (r : M ↝↝ N) →
                          ------------------------------------------------
                          (N , r) ∈ₗ all-reductions M
all-reductions-complete {M = let= return V `in N} (let-return .V .N) = Hd
all-reductions-complete {M = let= let= M `in L `in N} (context-let r) = f-∈ (λ {(L , r) → (let= L `in _) , context-let r}) (all-reductions-complete r)
all-reductions-complete {M = let= V · W `in N} (context-let r) = f-∈ (λ {(L , r) → (let= L `in _) , context-let r}) (all-reductions-complete r)
all-reductions-complete {M = let= ↑ op V M `in N} (let-↑ .V .M .N) = Hd
all-reductions-complete {M = let= ↑ op V M `in N} (context-let r) = Tl (f-∈ (λ {(L , r) → (let= L `in _) , context-let r}) (all-reductions-complete r))
all-reductions-complete {M = let= ↓ op V M `in N} (context-let r) = f-∈ (λ {(L , r) → (let= L `in _) , context-let r}) (all-reductions-complete r)
all-reductions-complete {M = let= promise op ↦ M `in L `in N} (let-promise .M .L .N) = Hd
all-reductions-complete {M = let= promise op ↦ M `in L `in N} (context-let r) = Tl (f-∈ (λ {(L , r) → (let= L `in _) , context-let r}) (all-reductions-complete r))
all-reductions-complete {M = let= await V until M `in N} (context-let r) = f-∈ (λ {(L , r) → (let= L `in _) , context-let r}) (all-reductions-complete r)
all-reductions-complete {M = ƛ M · W} (apply .M .W) = Hd
all-reductions-complete {M = ↑ op V M} (context-↑ r) = f-∈ (λ {(L , r) → ↑ _ _ L , context-↑ r}) (all-reductions-complete r)
all-reductions-complete {M = ↓ op V (return V')} (↓-return .V .V') = Hd
all-reductions-complete {M = ↓ op V (let= M `in N)} (context-↓ r) = f-∈ (λ {(L , r) → ↓ _ _ L , context-↓ r}) (all-reductions-complete r)
all-reductions-complete {M = ↓ op V (V' · W)} (context-↓ r) = f-∈ (λ {(L , r) → ↓ _ _ L , context-↓ r}) (all-reductions-complete r)
all-reductions-complete {M = ↓ op V (↑ op' V' M)} (↓-↑ .V .V' .M) = Hd
all-reductions-complete {M = ↓ op V (↑ op' V' M)} (context-↓ r) = Tl (f-∈ (λ {(L , r) → ↓ _ _ L , context-↓ r}) (all-reductions-complete r))
all-reductions-complete {M = ↓ op V (↓ op' V' M)} (context-↓ r) = f-∈ (λ {(L , r) → ↓ _ _ L , context-↓ r}) (all-reductions-complete r)
all-reductions-complete {M = ↓ op V (promise op' ↦ M `in N)} r with decₛ op op'
all-reductions-complete {M = ↓ op V (promise op' ↦ M `in N)} (↓-promise-op .V .M .N) | yes refl = Hd
all-reductions-complete {M = ↓ op V (promise op' ↦ M `in N)} (↓-promise-op' p .V .M .N) | yes refl = contradiction refl p
all-reductions-complete {M = ↓ op V (promise op' ↦ M `in N)} (context-↓ r) | yes refl = Tl (f-∈ (λ {(L , r) → ↓ _ _ L , context-↓ r}) (all-reductions-complete r))
all-reductions-complete {M = ↓ op V (promise op' ↦ M `in N)} (↓-promise-op .V .M .N) | no ¬≡ = contradiction refl ¬≡
all-reductions-complete {M = ↓ op V (promise op' ↦ M `in N)} (↓-promise-op' p .V .M .N) | no ¬≡ = Hd
all-reductions-complete {M = ↓ op V (promise op' ↦ M `in N)} (context-↓ r) | no ¬≡ = Tl (f-∈ (λ {(L , r) → ↓ _ _ L , context-↓ r}) (all-reductions-complete r))
all-reductions-complete {M = ↓ op V (await V' until M)} (context-↓ r) = f-∈ (λ {(L , r) → ↓ _ _ L , context-↓ r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in return V} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in (let= N `in L)} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in (V · W)} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in ↑ op' V N} (promise-↑ .V .M .N) = Hd
all-reductions-complete {M = promise op ↦ M `in ↑ op' V N} (context-promise r) = Tl (f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r))
all-reductions-complete {M = promise op ↦ M `in ↓ op' V N} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in (promise op' ↦ N `in L)} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in (await V until N)} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = await ⟨ V ⟩ until M} (await-promise .V .M) = Hd

f-∈-aux : {A B : Set}
          {x : A}
          {y : B}
          {xs : List A}
          (f : A → B) →
          x ∈ₗ xs →
          y ≡ f x →
          ----------------
          y ∈ₗ (mapₗ f xs)
f-∈-aux f x∈ refl = f-∈ f x∈

sn-decr : {Γ : Ctx}
          {X : Type}
          {M N : Γ ⊢M⦂ X} →
          SN M →
          M ↝↝ N →
          ----------------
          SN N
sn-decr (sn f) = f

max-lemma : {l : List ℕ}
            {m : ℕ} →
            m ∈ₗ l →
            -------------------
            m ≤ (foldr _⊔_ 0 l)
max-lemma {xs} {m} Hd = m≤m⊔n m _
max-lemma {x ∷ₗ xs} (Tl m∈) = m≤n⇒m≤o⊔n x (max-lemma m∈)

-- returns the length of the longest reduction sequence from M

max : {Γ : Ctx}
      {X : Type}
      (M : Γ ⊢M⦂ X) →
      SN M →
      --------------
      ℕ
max M (sn f) = foldr _⊔_ 0 (mapₗ (λ {(L , r) → suc (max L (f r))}) (all-reductions M))

max-decr : {Γ : Ctx}
           {X : Type}
           {M N : Γ ⊢M⦂ X}  
           (s : SN M)
           (r : M ↝↝ N) →
           -----------------------------------
           suc (max N (sn-decr s r)) ≤ max M s
max-decr {M = M} (sn f) r
  = max-lemma {(mapₗ (λ {(L , r) → suc (max L (f r))}) (all-reductions M))} (f-∈-aux (λ { (L , r) → suc (max L (f r)) }) (all-reductions-complete r) refl)

sni-≤ : {Γ : Ctx}
        {X : Type}
        {m n : ℕ}
        {M : Γ ⊢M⦂ X} →
        SNi m M →
        m ≤ n →
        ------------
        SNi n M
sni-≤ (sni f) (s≤s le) = sni (λ r → sni-≤ (f r) le)

sni-suc : {Γ : Ctx}
          {X : Type}
          {m : ℕ}
          {M : Γ ⊢M⦂ X} →
          SNi m M →
          ------------
          SNi (suc m) M
sni-suc (sni f) = sni (λ r → sni-suc (f r))

-- finally, the proof that if a term is SN then there exists a number bounding the length of reduction sequences

sn→sni : {Γ : Ctx}
         {X : Type}
         {M : Γ ⊢M⦂ X}
         (s : SN M) →
         ------------------
         SNi (suc (max M s)) M 
sn→sni (sn f) = sni (λ r → sni-≤ (sn→sni (f r)) (max-decr (sn f) r))

{-
-- maybe there's an easier way: we define a type of all one-step
-- reductions from a fixed term, and prove that it is finite (unfinished)

-record Reductions {Γ : Ctx} {X : Type} (M : Γ ⊢M⦂ X) : Set where
  field
    N : Γ ⊢M⦂ X
    r : M ↝↝ N

term-depth : {Γ : Ctx} {X : Type} (M : Γ ⊢M⦂ X) → ℕ
term-depth (return V) = zero
term-depth (let= M `in N) = suc (term-depth M)
term-depth (V · W) = zero
term-depth (↑ op V M) = suc (term-depth M)
term-depth (↓ op V M) = suc (term-depth M)
term-depth (promise op ↦ M `in N) = suc (term-depth N)
term-depth (await V until M) = zero

red-depth : {Γ : Ctx} {X : Type} {M N : Γ ⊢M⦂ X} → M ↝↝ N → ℕ
red-depth (apply M V) = zero
red-depth (let-return V N) = zero
red-depth (let-↑ V M N) = zero
red-depth (let-promise M₁ M₂ N) = zero
red-depth (promise-↑ V M N) = zero
red-depth (↓-return V W) = zero
red-depth (↓-↑ V W M) = zero
red-depth (↓-promise-op V M N) = zero
red-depth (↓-promise-op' p V M N) = zero
red-depth (await-promise V M) = zero
red-depth (context-let r) = suc (red-depth r)
red-depth (context-↑ r) = suc (red-depth r)
red-depth (context-↓ r) = suc (red-depth r)
red-depth (context-promise r) = suc (red-depth r)

mkFin : {m : ℕ} (n : ℕ) → Fin (n + suc m)
mkFin zero = 0F
mkFin (suc n) = sucF (mkFin n)

rd≤td : {Γ : Ctx} {X : Type} {M N : Γ ⊢M⦂ X} (r : M ↝↝ N) →
  red-depth r ≤ term-depth M

from : {Γ : Ctx} {X : Type} {M : Γ ⊢M⦂ X} → Reductions M → Fin (10 + term-depth M)
from record { N = N ; r = (apply M₁ V) } = mkFin 0
from record { N = N ; r = (let-return V N₁) } = mkFin 1
from record { N = N ; r = (let-↑ V M₁ N₁) } = mkFin 2
from record { N = N ; r = (let-promise M₁ M₂ N₁) } = mkFin 3
from record { N = N ; r = (promise-↑ V M₁ N₁) } = mkFin 4
from record { N = N ; r = (↓-return V W) } = mkFin 5
from record { N = N ; r = (↓-↑ V W M₁) } = mkFin 6
from record { N = N ; r = (↓-promise-op V M₁ N₁) } = mkFin 7
from record { N = N ; r = (↓-promise-op' p V M₁ N₁) } = mkFin 8
from record { N = N ; r = (await-promise V M₁) } = mkFin 9
from record { N = N ; r = (context-let r) } = inject≤ (fromℕ (10 + red-depth r)) (+-monoʳ-≤ 11 (rd≤td r))
from record { N = N ; r = (context-↑ r) } = inject≤ (fromℕ (10 + red-depth r)) (+-monoʳ-≤ 11 (rd≤td r))
from record { N = N ; r = (context-↓ r) } = inject≤ (fromℕ (10 + red-depth r)) (+-monoʳ-≤ 11 (rd≤td r))
from record { N = N ; r = (context-promise r) } = inject≤ (fromℕ (10 + red-depth r)) (+-monoʳ-≤ 11 (rd≤td r))

from-inj : {Γ : Ctx} {X : Type} {M : Γ ⊢M⦂ X} (a b : Reductions M) →
  from a ≡ from b → a ≡ b
from-inj record { N = N ; r = (apply M V) } record { N = N' ; r = (apply .M .V) } eq = refl
from-inj record { N = N ; r = (let-return V N₁) } record { N = N' ; r = (let-return .V .N₁) } eq = refl
from-inj record { N = N ; r = (let-↑ V M N₁) } record { N = N' ; r = (let-↑ .V .M .N₁) } eq = refl
from-inj record { N = N ; r = (let-promise M₁ M₂ N₁) } record { N = N' ; r = (let-promise .M₁ .M₂ .N₁) } eq = refl
from-inj record { N = N ; r = (promise-↑ V M N₁) } record { N = N' ; r = (promise-↑ .V .M .N₁) } eq = refl
from-inj record { N = N ; r = (↓-return V W) } record { N = N' ; r = (↓-return .V .W) } eq = refl
from-inj record { N = N ; r = (↓-↑ V W M) } record { N = N' ; r = (↓-↑ .V .W .M) } eq = refl
from-inj record { N = N ; r = (↓-promise-op V M N₁) } record { N = N' ; r = (↓-promise-op .V .M .N₁) } eq = refl
from-inj record { N = N ; r = (↓-promise-op' p V M N₁) } record { N = N' ; r = (↓-promise-op' p₁ .V .M .N₁) } eq = refl
from-inj record { N = N ; r = (await-promise V M) } record { N = N' ; r = (await-promise .V .M) } eq = refl
from-inj record { N = N ; r = (context-let r) } record { N = N' ; r = (context-let r') } eq = {!   !}
from-inj record { N = N ; r = (context-↑ r) } record { N = N' ; r = (context-↑ r') } eq = {!   !}
from-inj record { N = N ; r = (context-↓ r) } record { N = N' ; r = (context-↓ r') } eq = {!   !}
from-inj record { N = N ; r = (context-promise r) } record { N = N' ; r = (context-promise r') } eq = {!   !}

-}

sn-↑-i : {Γ : Ctx}
         {X : Type}
         {op : Σₛ}
         {V : Γ ⊢V⦂ ``(payload op)}
         {M : Γ ⊢M⦂ X} →
         SN M →
         -------------------------
         SN (↑ op V M)
sn-↑-i (sn f) = sn (λ {(context-↑ r) → sn-↑-i (f r)})

sn-↑-e : {Γ : Ctx}
         {X : Type}
         {op : Σₛ}
         {V : Γ ⊢V⦂ ``(payload op)}
         {M : Γ ⊢M⦂ X} →
         SN (↑ op V M) →
         -------------------------
         SN M
sn-↑-e (sn f) = sn (λ {r → sn-↑-e (f (context-↑ r))})

sni-↑-i : {Γ : Ctx}
          {X : Type}
          {m : ℕ}
          {op : Σₛ}
          {V : Γ ⊢V⦂ ``(payload op)}
          {M : Γ ⊢M⦂ X} →
          SNi m M →
          -------------------------
          SNi m (↑ op V M)
sni-↑-i (sni f) = sni (λ {(context-↑ r) → sni-↑-i (f r)})

sni-↑-e : {Γ : Ctx}
          {X : Type}
          {m : ℕ}
          {op : Σₛ}
          {V : Γ ⊢V⦂ ``(payload op)}
          {M : Γ ⊢M⦂ X} →
          SNi m (↑ op V M) →
          -------------------------
          SNi m M
sni-↑-e (sni f) = sni (λ {r → sni-↑-e (f (context-↑ r))})

sn-sub-e : {Γ Γ' : Ctx}
           {X : Type}
           {s : Sub Γ Γ'}
           {N : Γ ⊢M⦂ X} →
           SN (N [ s ]m) →
           ---------------
           SN N
sn-sub-e (sn f) = sn (λ r' → sn-sub-e (f (sub-↝↝ _ r')))

sn-ren-e : {Γ Γ' : Ctx}
           {X : Type}
           {M : Γ ⊢M⦂ X} →
           {rn : Ren Γ Γ'} →
           SN (M-rename rn M) →
           ------------------
           SN M
sn-ren-e (sn f) = sn (λ r' → sn-ren-e (f (ren-↝↝ _  r')))

data `M-rename_,_`↝↝_ : {Γ Γ' : Ctx} {X : Type} (rn : Ren Γ Γ') (M : Γ ⊢M⦂ X) (M' : Γ' ⊢M⦂ X) → Set where

  `ren : {Γ Γ' : Ctx}
         {X : Type}
         {M M' : Γ ⊢M⦂ X}
         (rn : Ren Γ Γ') →
         M ↝↝ M' →
         ----------------------------------
         `M-rename rn , M `↝↝ M-rename rn M'

strengthen-lemma-ren : {Γ Γ' : Ctx}
                       {X : Type}
                       {c : BType}
                       (rn : Ren Γ Γ')
                       (V : ((Γ ∷ ⟨ X ⟩) ⊢V⦂ Type.`` c)) →
                       -------------------------------------------
                       V-rename rn (strengthen-val {Δ = X ∷ₗ []} V) ≡ strengthen-val {Δ = X ∷ₗ []} (V-rename (wk₂ rn) V)
strengthen-lemma-ren rn (` Tl x) = refl
strengthen-lemma-ren rn (_⊢V⦂_.`` c) = refl

ren-↝↝' : {Γ Γ' : Ctx}
          {X : Type}
          {M : Γ ⊢M⦂ X} →
          {M' : Γ' ⊢M⦂ X} →
          {rn : Ren Γ Γ'} →
          M-rename rn M ↝↝ M' →
          -----------------------------
          `M-rename rn , M `↝↝ M'
ren-↝↝' {M = let= return V `in N} {rn = rn} (let-return _ _)
  rewrite commute-subst-rename-m {M = N} {s = `_ [ V ]s} {s' = `_ [ V-rename rn V ]s}
    {rΓ = wk₂ rn} {rΔ = rn} λ {Hd → refl; (Tl x) → refl}
  = `ren rn (let-return V N)
ren-↝↝' {M = let= let= M `in N `in L} (context-let r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-let r')
ren-↝↝' {M = let= V · W `in N} (context-let r) with ren-↝↝' r
... | `ren _ (apply M _) = `ren _ (context-let (apply M _))
ren-↝↝' {M = let= ↑ op V M `in N} (let-↑ _ _ _) = `ren _ (let-↑ V M N)
ren-↝↝' {M = let= ↑ op V M `in N} (context-let r) with ren-↝↝' r
... | `ren _ (context-↑ x) = `ren _ (context-let (context-↑ x))
ren-↝↝' {M = let= ↓ op V M `in N} (context-let r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-let r')
ren-↝↝' {M = let= promise op ↦ M `in N `in L} {rn = rn} (let-promise _ _ _)
  = subst (λ z → `M-rename _ , _ `↝↝ (promise _ ↦ _ `in (let= _ `in z)))
           (trans
             (trans
               (ren-ren-m {rn = comp-ren exchange wk₁} {rn' = wk₂ (wk₂ rn)} L)
               (cong-rename-m {r = comp-ren (wk₂ (wk₂ rn)) (comp-ren exchange wk₁) } λ {Hd → refl; (Tl x) → refl}))
             (sym (ren-ren-m {rn = wk₂ rn} {rn' = comp-ren (exchange) wk₁} L)))
           (`ren rn (let-promise M N L))
ren-↝↝' {M = let= promise op ↦ M `in N `in L} (context-let r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-let r')
ren-↝↝' {M = let= await V until M `in N} (context-let r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-let r')
ren-↝↝' {M = ƛ M · W} {rn = rn} (apply _ _)
  rewrite commute-subst-rename-m {M = M} {s = `_ [ W ]s} {s' = `_ [ V-rename rn W ]s}
    {rΓ = wk₂ rn} {rΔ = rn} λ {Hd → refl; (Tl x) → refl}
  = `ren rn (apply M W)
ren-↝↝' {M = ↑ op V M} (context-↑ r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-↑ r')
ren-↝↝' {M = ↓ op V (return V')} (↓-return _ _) = `ren _ (↓-return V V')
ren-↝↝' {M = ↓ op V (let= M `in N)} (context-↓ r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-↓ r')
ren-↝↝' {M = ↓ op V (V' · W)} (context-↓ r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-↓ r')
ren-↝↝' {M = ↓ op V (↑ op' V' M)} (↓-↑ _ _ _) = `ren _ (↓-↑ V V' M)
ren-↝↝' {M = ↓ op V (↑ op' V' M)} (context-↓ r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-↓ r')
ren-↝↝' {M = ↓ op V (↓ op' V' M)} (context-↓ r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-↓ r')
ren-↝↝' {M = ↓ op V (promise op' ↦ M `in N)} {rn = rn} (↓-promise-op _ _ _)
  rewrite commute-subst-rename-m {M = M}
    {s = id-subst [ V ]s} {s' = id-subst [ V-rename rn V ]s}
    {rΓ = (wk₂ rn)} {rΔ = rn}
    (λ {Hd → refl; (Tl x) → refl})
  = subst₂ (λ z w → `M-rename _ , _ `↝↝ (let= M-rename rn (M [ `_ [ V ]s ]m) `in ↓ op z w))
    ((trans 
      (trans
        (ren-ren-v {rn = wk₁} {rn' = wk₂ rn} V)
        (cong-rename-v {r = comp-ren (wk₂ rn) wk₁} {r' = comp-ren wk₁ rn} {V = V} (λ x → refl)))
      (sym (ren-ren-v V))))
      (trans
        (sym (commute-subst-rename-m {M = M-rename (comp-ren exchange wk₁) N}
               {s = id-subst [ ` Hd ]s}
               {rΔ = wk₂ rn}
               (λ {Hd → refl; (Tl x) → refl})))
        (cong (λ z → z [ id-subst [ ` Hd ]s ]m)
          (trans
            (trans
              (ren-ren-m {rn = comp-ren exchange wk₁} {rn' = wk₂ (wk₂ rn)} N)
              (cong-rename-m {r = comp-ren (wk₂ (wk₂ rn)) (comp-ren exchange wk₁) } λ {Hd → refl; (Tl x) → refl}))
            (sym (ren-ren-m {rn = wk₂ rn} {rn' = comp-ren (exchange) wk₁} N)))))
    (`ren rn (↓-promise-op V M N))
ren-↝↝' {M = ↓ op V (promise op' ↦ M `in N)} {rn = rn} (↓-promise-op' p _ _ _)
  = subst (λ z → `M-rename _ , _ `↝↝ (promise _ ↦ _ `in ↓ op z _))
    (trans 
      (trans
        (ren-ren-v {rn = wk₁} {rn' = wk₂ rn} V)
        (cong-rename-v {r = comp-ren (wk₂ rn) wk₁} {r' = comp-ren wk₁ rn} {V = V} (λ x → refl)))
     (sym (ren-ren-v V)))
    (`ren rn (↓-promise-op' p V M N))
ren-↝↝' {M = ↓ op V (promise op' ↦ M `in N)} (context-↓ r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-↓ r')
ren-↝↝' {M = ↓ op V (await V' until M)} (context-↓ r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-↓ r')
ren-↝↝' {M = promise op ↦ M `in return V} (context-promise ())
ren-↝↝' {M = promise op ↦ M `in (let= N `in L)} (context-promise r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-promise r')
ren-↝↝' {M = promise op ↦ M `in (V · W)} (context-promise r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-promise r')
ren-↝↝' {M = promise op ↦ M `in ↑ op' V N} {rn = rn} (promise-↑ _ _ _)
  rewrite (sym (strengthen-lemma-ren rn V))
  = `ren rn (promise-↑ V M N)
ren-↝↝' {M = promise op ↦ M `in ↑ op' V N} (context-promise r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-promise r')
ren-↝↝' {M = promise op ↦ M `in ↓ op' V N} (context-promise r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-promise r')
ren-↝↝' {M = promise op ↦ M `in (promise op' ↦ N `in L)} (context-promise r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-promise r')
ren-↝↝' {M = promise op ↦ M `in (await V until N)} (context-promise r) with ren-↝↝' r
... | `ren _ r' = `ren _ (context-promise r')
ren-↝↝' {M = await ⟨ V ⟩ until M} {rn = rn} (await-promise _ _)
  rewrite commute-subst-rename-m {M = M} {s = `_ [ V ]s} {s' = `_ [ V-rename rn V ]s}
    {rΓ = wk₂ rn} {rΔ = rn} λ {Hd → refl; (Tl x) → refl}
  = `ren rn (await-promise V M)

sn-ren-i' : {Γ Γ' : Ctx}
            {X : Type} 
            {M : Γ ⊢M⦂ X} →
            {rn : Ren Γ Γ'} →
            SN M →
            {L' : Γ' ⊢M⦂ X} →
            `M-rename rn , M `↝↝ L' →
            -------------------
            SN L' 
sn-ren-i' (sn f) (`ren _ x) = sn (λ r' → sn-ren-i' (f x) (ren-↝↝' r'))

sn-ren-i : {Γ Γ' : Ctx}
           {X : Type}
           {M : Γ ⊢M⦂ X} →
           {rn : Ren Γ Γ'} →
           SN M →
           ------------------
           SN (M-rename rn M)
sn-ren-i s = sn (λ r' → sn-ren-i' s (ren-↝↝' r'))