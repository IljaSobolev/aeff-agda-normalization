open import AEffStarSN.AEffStar
open import AEffStarSN.SubstitutionProperties

open import EffectAnnotations using (Σₛ; decₛ)
open import AEff using (payload; Σ-base; ar-base)
open import Types using (BType; dec-bty; GType)

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

module AEffStarSN.StrongNormalisation where

data SN : {Γ : Ctx} {X : Type} → Γ ⊢M⦂ X → Set where
  sn : {Γ : Ctx}
       {X : Type}
       {M : Γ ⊢M⦂ X} →
       ({N : Γ ⊢M⦂ X} → M ↝↝ N → SN N) →
       --------------------------------
       SN M

data SNi : {Γ : Ctx} {X : Type} → ℕ → Γ ⊢M⦂ X → Set where
  sni : {Γ : Ctx}
        {X : Type}
        {m : ℕ}
        {M : Γ ⊢M⦂ X} →
        ({N : Γ ⊢M⦂ X} → M ↝↝ N → SNi m N) →
        --------------------------------
        SNi (suc m) M

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
                {V : Γ ⊢V⦂ ```(payload op)}
                {M : Γ ⊢M⦂ X} →
                List (Σ[ L ∈ Γ ⊢M⦂ X ] M ↝↝ L) →
                ---------------------------
                List (Σ[ L ∈ Γ ⊢M⦂ X ] ↑ op V M ↝↝ L)
add-context-↑ xs = mapₗ (λ {(L , r) → ↑ _ _ L , context-↑ r}) xs

add-context-↓ : {Γ : Ctx}
                {X : Type}
                {op : Σₛ}
                {V : Γ ⊢V⦂ ```(payload op)}
                {M : Γ ⊢M⦂ X} →
                List (Σ[ L ∈ Γ ⊢M⦂ X ] M ↝↝ L) →
                ---------------------------
                List (Σ[ L ∈ Γ ⊢M⦂ X ] ↓ op V M ↝↝ L)
add-context-↓ xs = mapₗ (λ {(L , r) → ↓ _ _ L , context-↓ r}) xs

add-context-promise : {Γ : Ctx}
                      {X Y : Type}
                      {op : Σₛ}
                      {M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩} →
                      {N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y} →
                      List (Σ[ L ∈ Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ] N ↝↝ L) →
                      ---------------------------
                      List (Σ[ L ∈ Γ ⊢M⦂ Y ] promise op ↦ M `in N ↝↝ L)
add-context-promise xs = mapₗ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) xs

add-context-coerce : {Γ : Ctx}
                     {X : Type}
                     {N : Γ ⊢M⦂ X} →
                     List (Σ[ L ∈ Γ ⊢M⦂ X ] N ↝↝ L) →
                     ---------------------------
                     List (Σ[ L ∈ Γ ⊢M⦂ X ] coerce N ↝↝ L)
add-context-coerce xs = mapₗ (λ {(L , r) → coerce L , context-coerce r}) xs

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
all-reductions (let= coerce M `in L) = add-context-let (all-reductions (coerce M))
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
all-reductions (↓ op V (coerce M)) = add-context-↓ (all-reductions (coerce M))
all-reductions (promise op ↦ M `in return V) = []
all-reductions (promise op ↦ M `in (let= N `in L)) = add-context-promise (all-reductions (let= N `in L))
all-reductions (promise op ↦ M `in (V · W)) = add-context-promise (all-reductions (V · W))
all-reductions (promise op ↦ M `in ↑ op' V N) = ((_ , promise-↑ V M N)) ∷ₗ add-context-promise (all-reductions (↑ op' V N))
all-reductions (promise op ↦ M `in ↓ op' V N) = add-context-promise (all-reductions (↓ op' V N))
all-reductions (promise op ↦ M `in (promise op' ↦ N `in L)) = add-context-promise (all-reductions (promise op' ↦ N `in L))
all-reductions (promise op ↦ M `in (await V until N)) = add-context-promise (all-reductions (await V until N))
all-reductions (promise op ↦ M `in (coerce N)) = add-context-promise (all-reductions (coerce N))
all-reductions (await ` x until M) = []
all-reductions (await ⟨ V ⟩ until M) = ((_ , await-promise V M)) ∷ₗ []
all-reductions (await ★ until M) = []
all-reductions (coerce (return V)) = (_ , coerce-return V) ∷ₗ []
all-reductions (coerce (let= M `in N)) = add-context-coerce (all-reductions (let= M `in N))
all-reductions (coerce (V · W)) = add-context-coerce (all-reductions (V · W))
all-reductions (coerce (↑ op V M)) = (_ , coerce-↑ V M) ∷ₗ (add-context-coerce (all-reductions (↑ op V M)))
all-reductions (coerce (↓ op V M)) = add-context-coerce (all-reductions (↓ op V M))
all-reductions (coerce (promise op ↦ M `in N)) = (_ , coerce-promise M N) ∷ₗ (add-context-coerce (all-reductions (promise op ↦ M `in N)))
all-reductions (coerce (await V until M)) = add-context-coerce (all-reductions (await V until M))
all-reductions (coerce (coerce M)) = add-context-coerce (all-reductions (coerce M))

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
all-reductions-complete {M = let= coerce M `in N} (context-let r) = f-∈ (λ {(L , r) → (let= L `in _) , context-let r}) (all-reductions-complete r)
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
all-reductions-complete {M = ↓ op V (coerce M)} (context-↓ r) = f-∈ (λ {(L , r) → ↓ _ _ L , context-↓ r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in return V} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in (let= N `in L)} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in (V · W)} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in ↑ op' V N} (promise-↑ .V .M .N) = Hd
all-reductions-complete {M = promise op ↦ M `in ↑ op' V N} (context-promise r) = Tl (f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r))
all-reductions-complete {M = promise op ↦ M `in ↓ op' V N} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in (promise op' ↦ N `in L)} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in (await V until N)} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = promise op ↦ M `in (coerce N)} (context-promise r) = f-∈ (λ {(L , r) → promise _ ↦ _ `in L , context-promise r}) (all-reductions-complete r)
all-reductions-complete {M = await ⟨ V ⟩ until M} (await-promise .V .M) = Hd
all-reductions-complete {M = coerce (return V)} (coerce-return .V) = Hd
all-reductions-complete {M = coerce (let= M `in N)} (context-coerce r) = f-∈ (λ { (L , r) → coerce L , context-coerce r }) (all-reductions-complete r)
all-reductions-complete {M = coerce (V · W)} (context-coerce r) = f-∈ (λ { (L , r) → coerce L , context-coerce r }) (all-reductions-complete r)
all-reductions-complete {M = coerce (↑ op V M)} (context-coerce r) = Tl (f-∈ (λ { (L , r) → coerce L , context-coerce r }) (all-reductions-complete r))
all-reductions-complete {M = coerce (↑ op V M)} (coerce-↑ .V .M) = Hd
all-reductions-complete {M = coerce (↓ op V M)} (context-coerce r) = f-∈ (λ { (L , r) → coerce L , context-coerce r }) (all-reductions-complete r)
all-reductions-complete {M = coerce (promise op ↦ M `in N)} (context-coerce r) = Tl (f-∈ (λ { (L , r) → coerce L , context-coerce r }) (all-reductions-complete r))
all-reductions-complete {M = coerce (promise op ↦ M `in N)} (coerce-promise .M .N) = Hd
all-reductions-complete {M = coerce (await V until M)} (context-coerce r) = f-∈ (λ { (L , r) → coerce L , context-coerce r }) (all-reductions-complete r)
all-reductions-complete {M = coerce (coerce M)} (context-coerce r) = f-∈ (λ { (L , r) → coerce L , context-coerce r }) (all-reductions-complete r)

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

sn→sni : {Γ : Ctx}
         {X : Type}
         {M : Γ ⊢M⦂ X}
         (s : SN M) →
         ------------------
         SNi (suc (max M s)) M 
sn→sni (sn f) = sni (λ r → sni-≤ (sn→sni (f r)) (max-decr (sn f) r))

sn-↑-i : {Γ : Ctx}
         {X : Type}
         {op : Σₛ}
         {V : Γ ⊢V⦂ ```(payload op)}
         {M : Γ ⊢M⦂ X} →
         SN M →
         -------------------------
         SN (↑ op V M)
sn-↑-i (sn f) = sn (λ {(context-↑ r) → sn-↑-i (f r)})

sn-↑-e : {Γ : Ctx}
         {X : Type}
         {op : Σₛ}
         {V : Γ ⊢V⦂ ```(payload op)}
         {M : Γ ⊢M⦂ X} →
         SN (↑ op V M) →
         -------------------------
         SN M
sn-↑-e (sn f) = sn (λ {r → sn-↑-e (f (context-↑ r))})

sni-↑-e : {Γ : Ctx}
          {X : Type}
          {m : ℕ}
          {op : Σₛ}
          {V : Γ ⊢V⦂ ```(payload op)}
          {M : Γ ⊢M⦂ X} →
          SNi m (↑ op V M) →
          -------------------------
          SNi m M
sni-↑-e (sni f) = sni (λ {r → sni-↑-e (f (context-↑ r))})