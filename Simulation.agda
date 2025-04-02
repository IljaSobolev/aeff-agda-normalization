import AEffBsn.AEffB as AEff'

open import Types
open import AEff
open import Finality
open import Preservation
open import Renamings
open import Substitutions
open import EffectAnnotations

open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Relation.Nullary.Negation
import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])

-- injection of AEff into AEffB and a proof of SN using this injection

-- based on https://plfa.github.io/Bisimulation/

-- types

data _≡-ty-v_ : VType → AEff'.Type → Set
data _≡-ty-m_ : CType → AEff'.Type → Set

data _≡-ty-v_ where

  ``` : (x : GType) →
        ----------------------------
        (``` x) ≡-ty-v (AEff'.``` x)

  _⇒_ : {X : VType} {Y : CType}
        {X' Y' : AEff'.Type} →
        X ≡-ty-v X' →
        Y ≡-ty-m Y' →
        ------------------------------
        (X ⇒ Y) ≡-ty-v (X' AEff'.⇒ Y')

  ⟨_⟩ : {X : VType}
        {X' : AEff'.Type} →
        X ≡-ty-v X' →
        ---------------------------
        ⟨ X ⟩ ≡-ty-v (AEff'.⟨ X' ⟩)

data _≡-ty-m_ where

  _!_  : {X : VType}
         {o : O}
         {i : I}
         {X' : AEff'.Type} →
         X ≡-ty-v X' →
         -----------------------
         (X ! (o , i)) ≡-ty-m X'

-- contexts

data _≡-ctx_ : Ctx → AEff'.Ctx → Set where

  []  : -----------------
        [] ≡-ctx AEff'.[]

  _∷_ : {Γ : Ctx}
        {X : VType}
        {Γ' : AEff'.Ctx}
        {X' : AEff'.Type} →
        Γ ≡-ctx Γ' →
        X ≡-ty-v X' →
        -----------------------------
        (Γ ∷ X) ≡-ctx (Γ' AEff'.∷ X')

-- variables in contexts

data _≡-∈_ : {Γ : Ctx} {X : VType} {Γ' : AEff'.Ctx} {X' : AEff'.Type} → X ∈ Γ → X' AEff'.∈ Γ' → Set where

  Hd : {Γ : Ctx} {X : VType}
       {Γ' : AEff'.Ctx} {X' : AEff'.Type} →
       Γ ≡-ctx Γ' →
       X ≡-ty-v X' →
       -------------------------------------
       (Hd {X} {Γ}) ≡-∈ (AEff'.Hd {X'} {Γ'})

  Tl : {Γ : Ctx} {X Y : VType}
       {Γ' : AEff'.Ctx} {X' Y' : AEff'.Type} →
       {x : X ∈ Γ}
       {x' : X' AEff'.∈ Γ'} →
       x ≡-∈ x' →
       Y ≡-ty-v Y' →
       ---------------------------------------------------
       (Tl {X} {Γ} {Y} x) ≡-∈ (AEff'.Tl {X'} {Γ'} {Y'} x')

-- terms

data _≡-tm-v_ {Γ : Ctx} {Γ' : AEff'.Ctx} : {X : VType} → {X' : AEff'.Type} → Γ ⊢V⦂ X → Γ' AEff'.⊢V⦂ X' → Set
data _≡-tm-m_ {Γ : Ctx} {Γ' : AEff'.Ctx} : {X : CType} → {X' : AEff'.Type} → Γ ⊢M⦂ X → Γ' AEff'.⊢M⦂ X' → Set
  
data _≡-tm-v_ {Γ} {Γ'} where

  `_  : {X : VType} {X' : AEff'.Type}
        {x : X ∈ Γ}
        {x' : X' AEff'.∈ Γ'} →
        x ≡-∈ x' →
        -------------
        (` x) ≡-tm-v (AEff'.` x')

  ``_  : {x : Γ ≡-ctx Γ'} →
         (c : Σ-base) →
         --------------
         (`` c) ≡-tm-v (AEff'.`` c)
        
  ƛ   : {X : CType} {X' : AEff'.Type}
        {Y : VType} {Y' : AEff'.Type}
        {M : Γ ∷ Y ⊢M⦂ X} {M' : Γ' AEff'.∷ Y' AEff'.⊢M⦂ X'} →
        M ≡-tm-m M' →
        -------------
        (ƛ M) ≡-tm-v (AEff'.ƛ M')

  ⟨_⟩ : {X : VType} {X' : AEff'.Type}
        {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'} →
        V ≡-tm-v V' →
        -------------
        ⟨ V ⟩ ≡-tm-v AEff'.⟨ V' ⟩

data _≡-tm-m_ {Γ} {Γ'} where

  return           : {X : VType} {X' : AEff'.Type}
                     {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'}
                     {o : O}
                     {i : I} →
                     V ≡-tm-v V' →
                     -----------------
                     (return {o = o} {i = i} V) ≡-tm-m (AEff'.return V')

  let=_`in_        : {X Y : VType}
                     {X' Y' : AEff'.Type}
                     {o : O}
                     {i : I} → 
                     {M : Γ ⊢M⦂ X ! (o , i)} →
                     {M' : Γ' AEff'.⊢M⦂ X'} →
                     {N : Γ ∷ X ⊢M⦂ Y ! (o , i)} →
                     {N' : Γ' AEff'.∷ X' AEff'.⊢M⦂ Y'} →
                     M ≡-tm-m M' →
                     N ≡-tm-m N' →
                     -----------------------
                     (let= M `in N) ≡-tm-m (AEff'.let= M' `in N')

  _·_              : {X : VType} {X' : AEff'.Type}
                     {C : CType} {C' : AEff'.Type} 
                     {V : Γ ⊢V⦂ X ⇒ C} {V' : Γ' AEff'.⊢V⦂ X' AEff'.⇒ C'}
                     {W : Γ ⊢V⦂ X} {W' : Γ' AEff'.⊢V⦂ X'} →
                     V ≡-tm-v V' →
                     W ≡-tm-v W' →
                     -------------
                     (V · W) ≡-tm-m (V' AEff'.· W')

  ↑                : {X : VType} {X' : AEff'.Type}
                     {o : O}
                     {i : I}
                     (op : Σₛ)
                     (p : op ∈ₒ o)
                     {V : Γ ⊢V⦂ ```(payload op)} {V' : Γ' AEff'.⊢V⦂ AEff'.```(payload op)}
                     {M : Γ ⊢M⦂ X ! (o , i)} {M' : Γ' AEff'.⊢M⦂ X'} →
                     V ≡-tm-v V' →
                     M ≡-tm-m M' →
                     ----------------------
                     (↑ op p V M) ≡-tm-m (AEff'.↑ op V' M')

  ↓                : {X : VType} {X' : AEff'.Type}
                     {o : O}
                     {i : I}
                     (op : Σₛ)
                     {V : Γ ⊢V⦂ ```(payload op)} {V' : Γ' AEff'.⊢V⦂ AEff'.```(payload op)}
                     {M : Γ ⊢M⦂ X ! (o , i)} {M' : Γ' AEff'.⊢M⦂ X'} →
                     V ≡-tm-v V' →
                     M ≡-tm-m M' →
                     ----------------------
                     (↓ op V M) ≡-tm-m (AEff'.↓ op V' M')

  promise_∣_↦_`in_ : {X Y : VType} {X' Y' : AEff'.Type}
                     {o o' : O}
                     {i i' : I} 
                     (op : Σₛ)
                     (p : lkpᵢ op i ≡ just (o' , i'))
                     {M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i')}
                     {M' : Γ' AEff'.∷ AEff'.```(payload op) AEff'.⊢M⦂ AEff'.⟨ X' ⟩}
                     {N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)}
                     {N' : Γ' AEff'.∷ AEff'.⟨ X' ⟩ AEff'.⊢M⦂ Y'} →
                     M ≡-tm-m M' →
                     N ≡-tm-m N' →
                     ------------------------------------------
                     (promise op ∣ p ↦ M `in N) ≡-tm-m (AEff'.promise op ↦ M' `in N')

  await_until_     : {X : VType} {X' : AEff'.Type}
                     {C : CType} {C' : AEff'.Type}
                     {V : Γ ⊢V⦂ ⟨ X ⟩} {V' : Γ' AEff'.⊢V⦂ AEff'.⟨ X' ⟩}
                     {M : Γ ∷ X ⊢M⦂ C} {M' : Γ' AEff'.∷ X' AEff'.⊢M⦂ C'} →
                     V ≡-tm-v V' →
                     M ≡-tm-m M' →
                     --------------
                     (await V until M) ≡-tm-m (AEff'.await V' until M')

  {-coerce           : {X : VType}
                     {o o' : O}
                     {i i' : I} →
                     o ⊑ₒ o' →
                     i ⊑ᵢ i' → 
                     Γ ⊢M⦂ X ! (o , i) →
                     -------------------
                     Γ ⊢M⦂ X ! (o' , i')-}

-- renamings

data _≡-ren_ : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx} → Ren Γ Δ → AEff'.Ren Γ' Δ' → Set where

  ≡-ren-cons : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
               {rn : Ren Γ Δ} {rn' : AEff'.Ren Γ' Δ'} →
               Γ ≡-ctx Γ' →
               Δ ≡-ctx Δ' →
               ({X : VType} {X' : AEff'.Type}
                  {x : X ∈ Γ} {x' : X' AEff'.∈ Γ'} →
                  x ≡-∈ x' →
                  rn x ≡-∈ rn' x') →
               -----------------
               rn ≡-ren rn'

-- substitutions

data _≡-sub_ : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx} → Sub Γ Δ → AEff'.Sub Γ' Δ' → Set where

  ≡-sub-cons : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
               {s : Sub Γ Δ} {s' : AEff'.Sub Γ' Δ'} →
               Γ ≡-ctx Γ' →
               Δ ≡-ctx Δ' →
               ({X : VType} {X' : AEff'.Type}
                  {x : X ∈ Γ} {x' : X' AEff'.∈ Γ'} →
                  x ≡-∈ x' →
                  s x ≡-tm-v s' x') →
               -----------------
               s ≡-sub s'

-- equivalent variables have equivalent contexts

≡-ctx-∈ : {Γ : Ctx} {Γ' : AEff'.Ctx}
          {X : VType} {X' : AEff'.Type} →
          {x : X ∈ Γ} {x' : X' AEff'.∈ Γ'} →
          x ≡-∈ x' →
          ----------------
          Γ ≡-ctx Γ'
≡-ctx-∈ (Hd x X) = x ∷ X
≡-ctx-∈ (Tl x X) = ≡-ctx-∈ x ∷ X

-- equivalent terms have equivalent contexts

≡-ctx-tm-v : {Γ : Ctx} {Γ' : AEff'.Ctx}
             {X : VType} {X' : AEff'.Type}
             {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'} →
             V ≡-tm-v V' →
             ----------------
             Γ ≡-ctx Γ'

≡-ctx-tm-m : {Γ : Ctx} {Γ' : AEff'.Ctx}
             {X : CType} {X' : AEff'.Type}
             {M : Γ ⊢M⦂ X} {M' : Γ' AEff'.⊢M⦂ X'} →
             M ≡-tm-m M' →
             ----------------
             Γ ≡-ctx Γ'

≡-ctx-tm-v (` x) = ≡-ctx-∈ x
≡-ctx-tm-v (``_ {Γ} c) = Γ
≡-ctx-tm-v (ƛ M) with ≡-ctx-tm-m M
... | Γ ∷ _ = Γ
≡-ctx-tm-v ⟨ V ⟩ = ≡-ctx-tm-v V

≡-ctx-tm-m (return V) = ≡-ctx-tm-v V
≡-ctx-tm-m (let= _ `in N) with ≡-ctx-tm-m N
... | Γ ∷ _ = Γ
≡-ctx-tm-m (V · _) = ≡-ctx-tm-v V
≡-ctx-tm-m (↑ _ _ _ M) = ≡-ctx-tm-m M
≡-ctx-tm-m (↓ _ _ M) = ≡-ctx-tm-m M
≡-ctx-tm-m (promise _ ∣ _ ↦ _ `in N) with ≡-ctx-tm-m N
... | Γ ∷ _ = Γ
≡-ctx-tm-m (await _ until M) with ≡-ctx-tm-m M
... | Γ ∷ _ = Γ

-- equivalent variables have equivalent types

≡-ty-∈ : {Γ : Ctx} {Γ' : AEff'.Ctx}
         {X : VType} {X' : AEff'.Type}
         {x : X ∈ Γ} {x' : X' AEff'.∈ Γ'} →
         x ≡-∈ x' →
         ----------------
         X ≡-ty-v X'
≡-ty-∈ (Hd _ X) = X
≡-ty-∈ (Tl x _) = ≡-ty-∈ x

-- equivalent terms have equivalent types

≡-ty-tm-v : {Γ : Ctx} {Γ' : AEff'.Ctx}
            {X : VType} {X' : AEff'.Type}
            {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'} →
            V ≡-tm-v V' →
            ----------------
            X ≡-ty-v X' 

≡-ty-tm-m : {Γ : Ctx} {Γ' : AEff'.Ctx}
            {X : CType} {X' : AEff'.Type}
            {M : Γ ⊢M⦂ X} {M' : Γ' AEff'.⊢M⦂ X'} →
            M ≡-tm-m M' →
            ----------------
            X ≡-ty-m X' 

≡-ty-tm-v (` x) = ≡-ty-∈ x
≡-ty-tm-v (`` c) = ``` (ar-base c)
≡-ty-tm-v (ƛ M) with ≡-ctx-tm-m M
... | _ ∷ X = X ⇒ (≡-ty-tm-m M)
≡-ty-tm-v ⟨ V ⟩ = ⟨ ≡-ty-tm-v V ⟩

≡-ty-tm-m (return V) = _!_ (≡-ty-tm-v V)
≡-ty-tm-m (let= M `in N) = ≡-ty-tm-m N
≡-ty-tm-m (V · W) with ≡-ty-tm-v V
... | _ ⇒ X = X
≡-ty-tm-m (↑ _ _ _ M) = ≡-ty-tm-m M
≡-ty-tm-m (↓ op x M) with ≡-ty-tm-m M
... | _!_ X = _!_ X
≡-ty-tm-m (promise _ ∣ _ ↦ _ `in N) = ≡-ty-tm-m N
≡-ty-tm-m (await _ until M) = ≡-ty-tm-m M

≡-wk₂ : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
        {X : VType} {X' : AEff'.Type}
        {rn : Ren Γ Δ} {rn' : AEff'.Ren Γ' Δ'} →
        X ≡-ty-v X' →
        rn ≡-ren rn' →
        wk₂ {X = X} rn ≡-ren AEff'.wk₂ {X = X'} rn'
≡-wk₂ X (≡-ren-cons Γ Δ f) =
  ≡-ren-cons (Γ ∷ X) (Δ ∷ X) (λ {(Hd x Y) → Hd Δ X; (Tl x Y) → Tl (f x) Y})

≡-rn-v : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
         {X : VType} {X' : AEff'.Type}
         {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'}
         {rn : Ren Γ Δ} {rn' : AEff'.Ren Γ' Δ'} →
         V ≡-tm-v V' →
         rn ≡-ren rn' →
         ------------------------------------------
         V-rename rn V ≡-tm-v AEff'.V-rename rn' V'

≡-rn-m : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
         {X : CType} {X' : AEff'.Type}
         {M : Γ ⊢M⦂ X} {M' : Γ' AEff'.⊢M⦂ X'}
         {rn : Ren Γ Δ} {rn' : AEff'.Ren Γ' Δ'} →
         M ≡-tm-m M' →
         rn ≡-ren rn' →
         ------------------------------------------
         M-rename rn M ≡-tm-m AEff'.M-rename rn' M'

≡-rn-lift : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
            {X : VType} {X' : AEff'.Type}
            {Y : CType} {Y' : AEff'.Type}
            {rn : Ren Γ Δ} {rn' : AEff'.Ren Γ' Δ'} →
            {M : Γ ∷ X ⊢M⦂ Y} {M' : Γ' AEff'.∷ X' AEff'.⊢M⦂ Y'} →
            M ≡-tm-m M' →
            rn ≡-ren rn' →
            ------------------------------
            M-rename (wk₂ rn) M ≡-tm-m AEff'.M-rename (AEff'.wk₂ rn') M'
≡-rn-lift M rn with ≡-ctx-tm-m M
... | u ∷ X = ≡-rn-m M (≡-wk₂ X rn)

≡-rn-v (` x) (≡-ren-cons _ _ f) = ` f x
≡-rn-v (`` c) (≡-ren-cons _ Δ _) = ``_ {x = Δ} c
≡-rn-v (ƛ M) rn = ƛ (≡-rn-lift M rn)
≡-rn-v (⟨ V ⟩) rn = ⟨ ≡-rn-v V rn ⟩

≡-rn-m (return V) rn = return (≡-rn-v V rn)
≡-rn-m (let= M `in N) rn = let= (≡-rn-m M rn) `in (≡-rn-lift N rn)
≡-rn-m (V · W) rn = (≡-rn-v V rn) · ≡-rn-v W rn
≡-rn-m (↑ op p V M) rn = ↑ op p (≡-rn-v V rn) (≡-rn-m M rn)
≡-rn-m (↓ op V M) rn = ↓ op (≡-rn-v V rn) (≡-rn-m M rn)
≡-rn-m (promise op ∣ p ↦ M `in N) rn = promise op ∣ p ↦ (≡-rn-lift M rn) `in (≡-rn-lift N rn)
≡-rn-m (await V until M) rn = await (≡-rn-v V rn) until (≡-rn-lift M rn)

≡-lift : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
         {X : VType} {X' : AEff'.Type} →
         {s : Sub Γ Δ} {s' : AEff'.Sub Γ' Δ'} →
         X ≡-ty-v X' →
         s ≡-sub s' →
         lift {X = X} s ≡-sub AEff'.lift {X = X'} s'
≡-lift X (≡-sub-cons Γ Δ f)
  = ≡-sub-cons (Γ ∷ X) (Δ ∷ X) (λ {(Hd x Y) → ` (Hd Δ X); (Tl x Y) → ≡-rn-v (f x) (≡-ren-cons Δ (Δ ∷ Y) (λ z → Tl z X))})

≡-id-subst : {Γ : Ctx} {Γ' : AEff'.Ctx}
             {X : VType} {X' : AEff'.Type}
             {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'} →
             Γ ≡-ctx Γ' →
             X ≡-ty-v X' →
             V ≡-tm-v V' →
             -----------------------
             (id-subst {Γ} [ V ]s) ≡-sub (AEff'.id-subst {Γ'} AEff'.[ V' ]s)
≡-id-subst Γ X V = ≡-sub-cons (Γ ∷ X) Γ (λ {(Hd _ _) → V; (Tl x _) → ` x})

≡-sub-v : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
          {X : VType} {X' : AEff'.Type}
          {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'}
          {s : Sub Γ Δ}
          {s' : AEff'.Sub Γ' Δ'} →
          V ≡-tm-v V' →
          s ≡-sub s' →
          ----------------------------
          (V [ s ]v) ≡-tm-v (V' AEff'.[ s' ]v)

≡-sub-m : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
          {X : CType} {X' : AEff'.Type}
          {M : Γ ⊢M⦂ X} {M' : Γ' AEff'.⊢M⦂ X'}
          {s : Sub Γ Δ}
          {s' : AEff'.Sub Γ' Δ'} →
          M ≡-tm-m M' →
          s ≡-sub s' →
          ----------------------------
          (M [ s ]m) ≡-tm-m (M' AEff'.[ s' ]m)

≡-sub-lift : {Γ Δ : Ctx} {Γ' Δ' : AEff'.Ctx}
             {X : VType} {X' : AEff'.Type}
             {Y : CType} {Y' : AEff'.Type}
             {s : Sub Γ Δ} {s' : AEff'.Sub Γ' Δ'} →
             {M : Γ ∷ X ⊢M⦂ Y} {M' : Γ' AEff'.∷ X' AEff'.⊢M⦂ Y'} →
             M ≡-tm-m M' →
             s ≡-sub s' →
             -----------------------------
             (M [ lift s ]m) ≡-tm-m (M' AEff'.[ AEff'.lift s' ]m)
≡-sub-lift M s with ≡-ctx-tm-m M
... | _ ∷ X = ≡-sub-m M (≡-lift X s)

≡-sub-v (` x) (≡-sub-cons _ _ f) = f x
≡-sub-v (`` c) (≡-sub-cons _ Δ _) = ``_ {x = Δ} c
≡-sub-v (ƛ M) s = ƛ (≡-sub-lift M s)
≡-sub-v ⟨ V ⟩ s = ⟨ ≡-sub-v V s ⟩

≡-sub-m (return V) s = return (≡-sub-v V s)
≡-sub-m (let= M `in N) s = let= (≡-sub-m M s) `in (≡-sub-lift N s)
≡-sub-m (V · W) s = (≡-sub-v V s) · (≡-sub-v W s)
≡-sub-m (↑ op p V M) s = ↑ op p (≡-sub-v V s) (≡-sub-m M s)
≡-sub-m (↓ op V M) s = ↓ op (≡-sub-v V s) (≡-sub-m M s)
≡-sub-m (promise op ∣ p ↦ M `in N) s = promise op ∣ p ↦ (≡-sub-lift M s) `in (≡-sub-lift N s)
≡-sub-m (await V until M) s = await (≡-sub-v V s) until (≡-sub-lift M s)

≡-subst-v : {Γ : Ctx} {Γ' : AEff'.Ctx}
            {X : VType} {X' : AEff'.Type}
            {Y : VType} {Y' : AEff'.Type}
            {V : (Γ ∷ X) ⊢V⦂ Y} {V' : (Γ' AEff'.∷ X') AEff'.⊢V⦂ Y'}
            {W : Γ ⊢V⦂ X} {W' : Γ' AEff'.⊢V⦂ X'} →
            V ≡-tm-v V' →
            W ≡-tm-v W' →
            ----------------------
            V [ id-subst [ W ]s ]v ≡-tm-v V' AEff'.[ AEff'.id-subst AEff'.[ W' ]s ]v
≡-subst-v V W = ≡-sub-v V (≡-id-subst (≡-ctx-tm-v W) (≡-ty-tm-v W) W)

≡-subst-m : {Γ : Ctx} {Γ' : AEff'.Ctx}
            {X : VType} {X' : AEff'.Type}
            {Y : CType} {Y' : AEff'.Type}
            {M : (Γ ∷ X) ⊢M⦂ Y} {M' : (Γ' AEff'.∷ X') AEff'.⊢M⦂ Y'}
            {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'} →
            M ≡-tm-m M' →
            V ≡-tm-v V' →
            ----------------------
            M [ id-subst [ V ]s ]m ≡-tm-m M' AEff'.[ AEff'.id-subst AEff'.[ V' ]s ]m
≡-subst-m M V = ≡-sub-m M (≡-id-subst (≡-ctx-tm-v V) (≡-ty-tm-v V) V)

s-v : {Γ : Ctx} {Γ' : AEff'.Ctx}
      {X : VType} {X' : AEff'.Type}
      {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'} →
      V ≡-tm-v V' →
      Γ ⊢V⦂ X
s-v {V = V} _ = V

s-m : {Γ : Ctx} {Γ' : AEff'.Ctx}
      {X : CType} {X' : AEff'.Type}
      {M : Γ ⊢M⦂ X} {M' : Γ' AEff'.⊢M⦂ X'} →
      M ≡-tm-m M' →
      Γ ⊢M⦂ X
s-m {M = M} _ = M
    
t-v : {Γ : Ctx} {Γ' : AEff'.Ctx}
      {X : VType} {X' : AEff'.Type}
      {V : Γ ⊢V⦂ X} {V' : Γ' AEff'.⊢V⦂ X'} →
      V ≡-tm-v V' →
      Γ' AEff'.⊢V⦂ X'
t-v {V' = V'} _ = V'

t-m : {Γ : Ctx} {Γ' : AEff'.Ctx}
      {X : CType} {X' : AEff'.Type}
      {M : Γ ⊢M⦂ X} {M' : Γ' AEff'.⊢M⦂ X'} →
      M ≡-tm-m M' →
      Γ' AEff'.⊢M⦂ X'
t-m {M' = M'} _ = M'

sim : {Γ : Ctx} {Γ' : AEff'.Ctx}
      {X : CType} {X' : AEff'.Type}
      {M N : Γ ⊢M⦂ X} →
      {M' : Γ' AEff'.⊢M⦂ X'} →
      M ↝↝ N →
      M ≡-tm-m M' →
      -------------------
      Σ[ N' ∈ (Γ' AEff'.⊢M⦂ X') ] (N ≡-tm-m N') × (M' AEff'.↝↝ N')
{-sim (apply _ _) (ƛ M · W)
  = (t-m M) AEff'.[ AEff'.id-subst AEff'.[ t-v W ]s ]m , (≡-sub-m M (≡-id-subst (≡-ctx-tm-v W) (≡-ty-tm-v W) W)) , AEff'.apply (t-m M) (t-v W)
sim (let-return _ _) (let= return V `in N)
  = t-m N AEff'.[ AEff'.id-subst AEff'.[ t-v V ]s ]m , ≡-sub-m N (≡-id-subst (≡-ctx-tm-v V) (≡-ty-tm-v V) V) , AEff'.let-return (t-v V) (t-m N)
sim (let-↑ _ _ _ _) (let= ↑ _ _ V M `in N) = AEff'.↑ _ _ (AEff'.let= _ `in _) , ↑ _ _ V (let= M `in N) , AEff'.let-↑ _ _ _
sim (let-promise _ _ _ _) (let= promise _ ∣ _ ↦ M `in N `in L) = {!   !}
sim (promise-↑ _ _ _ _ _) (promise _ ∣ _ ↦ M `in ↑ _ _ V N) = {!   !}
sim (↓-return _ _) (↓ _ V (return W)) = AEff'.return _ , return W , AEff'.↓-return _ _
sim (↓-↑ _ _ _ _) (↓ _ V (↑ _ _ W M)) = AEff'.↑ _ _ (AEff'.↓ _ _ _) , ↑ _ _ W (↓ _ V M) , AEff'.↓-↑ _ _ _
sim (↓-promise-op _ _ _ _) (↓ _ V (promise _ ∣ _ ↦ M `in N))
  = {!   !} , ((let= {!   !} `in (↓ _ (≡-rn-v V {!   !}) (≡-sub-m (≡-rn-m N {!   !}) (≡-id-subst {!   !} {!   !} (` (Hd (≡-ctx-tm-v V) ⟨ {! ≡-ty-tm-m M  !} ⟩)))))) , {!   !})
sim (↓-promise-op' p q V M N) M≡M' = {!   !}
sim (await-promise V M) M≡M' = {!   !}
sim (context-let r) (let= M `in N) with sim r M
... | M' , M , r' = (AEff'.let= M' `in _) , (let= M `in N) , AEff'.context-let r'
sim (context-↑ r) (↑ _ _ V M) with sim r M
... | M' , M , r' = AEff'.↑ _ _ M' , ↑ _ _ V M , AEff'.context-↑ r'
sim (context-↓ r) (↓ _ V M) with sim r M
... | M' , M , r' = AEff'.↓ _ _ M' , ↓ _ V M , AEff'.context-↓ r'
sim (context-promise r) (promise _ ∣ _ ↦ _ `in N) with sim r N
... | N' , N , r' = (AEff'.promise _ ↦ _ `in N') , (promise _ ∣ _ ↦ _ `in N) , AEff'.context-promise r'
-} 