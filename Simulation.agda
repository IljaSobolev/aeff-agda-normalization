import AEffStarSN.AEffStar as B
open import AEffStarSN.StrongNormalisation renaming (SN to SN')
open import AEffStarSN.Reducibility renaming (all-terms-sn to all-terms-sn')

open import Types
open import AEff
open import Finality
open import Preservation
open import Renamings
open import Substitutions
open import EffectAnnotations

open import Data.Product
open import Data.Maybe
open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Relation.Binary.PropositionalEquality hiding ([_])

module Simulation where

data _~-ty-v_ : VType → B.Type → Set
data _~-ty-m_ : CType → B.Type → Set

data _~-ty-v_ where
  ~```  : (x : GType) →
          ------------------------
          (``` x) ~-ty-v (B.``` x)

  _~⇒_ : {X : VType} {X† : B.Type} →
          {Y : CType} {Y† : B.Type} →
          X ~-ty-v X† →
          Y ~-ty-m Y† →
          ------------------------------
          (X ⇒ Y) ~-ty-v (X† B.⇒ Y†)

  ~⟨_⟩  : {X : VType} {X† : B.Type} →
          X ~-ty-v X† →
          ---------------------------
          ⟨ X ⟩ ~-ty-v (B.⟨ X† ⟩)

data _~-ty-m_ where
  ~!  : {X : VType} {X† : B.Type}
        {o : O}
        {i : I} →
        X ~-ty-v X† →
        -----------------------
        (X ! (o , i)) ~-ty-m X†

data _~-ctx_ : Ctx → B.Ctx → Set where
  ~[]  : -----------------
         [] ~-ctx B.[]

  _~∷_ : {Γ : Ctx} {Γ† : B.Ctx}
         {X : VType} {X† : B.Type} →
         Γ ~-ctx Γ† →
         X ~-ty-v X† →
         -----------------------------
         (Γ ∷ X) ~-ctx (Γ† B.∷ X†)

data _~-bctx_ : BCtx → B.BCtx → Set where
  ~[]  : -----------------
         [] ~-bctx []

  _~∷_ : {Δ : BCtx} {Δ† : B.BCtx}
         {X : VType} {X† : B.Type} →
         X ~-ty-v X† →
         Δ ~-bctx Δ† →
         -----------------------------
         (X ∷ₗ Δ) ~-bctx (X† ∷ₗ Δ†)

data _~-∈_ : {Γ : Ctx} {X : VType} {Γ† : B.Ctx} {X† : B.Type} → X ∈ Γ → X† B.∈ Γ† → Set where
  ~Hd : {Γ : Ctx} {Γ† : B.Ctx}
        {X : VType} {X† : B.Type} →
        Γ ~-ctx Γ† →
        X ~-ty-v X† →
        -------------------------------------
        (Hd {X} {Γ}) ~-∈ (B.Hd {X†} {Γ†})

  ~Tl : {Γ : Ctx} {Γ† : B.Ctx} 
        {X Y : VType} {X† Y† : B.Type}
        {x : X ∈ Γ} {x† : X† B.∈ Γ†} →
        x ~-∈ x† →
        Y ~-ty-v Y† →
        ----------------------------------------------
        (Tl {X} {Γ} {Y} x) ~-∈ (B.Tl {X†} {Γ†} {Y†} x†)

data _~-tm-v_ {Γ : Ctx} {Γ† : B.Ctx} : {X : VType} {X† : B.Type} → Γ ⊢V⦂ X → Γ† B.⊢V⦂ X† → Set
data _~-tm-m_ {Γ : Ctx} {Γ† : B.Ctx} : {X : CType} {X† : B.Type} → Γ ⊢M⦂ X → Γ† B.⊢M⦂ X† → Set
  
data _~-tm-v_ {Γ} {Γ†} where
  ~`_  : {X : VType} {X† : B.Type}
         {x : X ∈ Γ} {x† : X† B.∈ Γ†} →
         x ~-∈ x† →
         -------------
         (` x) ~-tm-v (B.` x†)

  ~``_  : {x : Γ ~-ctx Γ†}
          (c : Σ-base) →
          --------------
          (`` c) ~-tm-v (B.`` c)
        
  ~ƛ   : {X : CType} {X† : B.Type}
         {Y : VType} {Y† : B.Type}
         {M : Γ ∷ Y ⊢M⦂ X} {M† : Γ† B.∷ Y† B.⊢M⦂ X†} →
         M ~-tm-m M† →
         -------------
         (ƛ M) ~-tm-v (B.ƛ M†)

  ~⟨_⟩ : {X : VType} {X† : B.Type}
         {V : Γ ⊢V⦂ X} {V† : Γ† B.⊢V⦂ X†} →
         V ~-tm-v V† →
         -------------
         ⟨ V ⟩ ~-tm-v B.⟨ V† ⟩

data _~-tm-m_ {Γ} {Γ†} where
  ~return            : {X : VType} {X† : B.Type}
                       {V : Γ ⊢V⦂ X} {V† : Γ† B.⊢V⦂ X†}
                       {o : O}
                       {i : I} →
                       V ~-tm-v V† →
                       -----------------
                       (return {o = o} {i = i} V) ~-tm-m (B.return V†)

  ~let=_`in_         : {X Y : VType} {X† Y† : B.Type}
                       {o : O}
                       {i : I}
                       {M : Γ ⊢M⦂ X ! (o , i)} {M† : Γ† B.⊢M⦂ X†} →
                       {N : Γ ∷ X ⊢M⦂ Y ! (o , i)} {N† : Γ† B.∷ X† B.⊢M⦂ Y†} →
                       M ~-tm-m M† →
                       N ~-tm-m N† →
                       -----------------------
                       (let= M `in N) ~-tm-m (B.let= M† `in N†)

  _~·_               : {X : VType} {X† : B.Type}
                       {C : CType} {C' : B.Type} 
                       {V : Γ ⊢V⦂ X ⇒ C} {V† : Γ† B.⊢V⦂ X† B.⇒ C'}
                       {W : Γ ⊢V⦂ X} {W† : Γ† B.⊢V⦂ X†} →
                       V ~-tm-v V† →
                       W ~-tm-v W† →
                       -------------
                       (V · W) ~-tm-m (V† B.· W†)

  ~↑                 : {X : VType} {X† : B.Type}
                       {o : O}
                       {i : I}
                       (op : Σₛ)
                       (p : op ∈ₒ o)
                       {V : Γ ⊢V⦂ ```(payload op)} {V† : Γ† B.⊢V⦂ B.```(payload op)}
                       {M : Γ ⊢M⦂ X ! (o , i)} {M† : Γ† B.⊢M⦂ X†} →
                       V ~-tm-v V† →
                       M ~-tm-m M† →
                       ----------------------
                       (↑ op p V M) ~-tm-m (B.↑ op V† M†)

  ~↓                 : {X : VType} {X† : B.Type}
                       {o : O}
                       {i : I}
                       (op : Σₛ)
                       {V : Γ ⊢V⦂ ```(payload op)} {V† : Γ† B.⊢V⦂ B.```(payload op)}
                       {M : Γ ⊢M⦂ X ! (o , i)} {M† : Γ† B.⊢M⦂ X†} →
                       V ~-tm-v V† →
                       M ~-tm-m M† →
                       ----------------------
                       (↓ op V M) ~-tm-m (B.↓ op V† M†)

  ~promise_∣_↦_`in_ : {X Y : VType} {X† Y† : B.Type}
                       {o o' : O}
                       {i i' : I} 
                       (op : Σₛ)
                       (p : lkpᵢ op i ≡ just (o' , i'))
                       {M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i')}
                       {M† : Γ† B.∷ B.```(payload op) B.⊢M⦂ B.⟨ X† ⟩}
                       {N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)}
                       {N† : Γ† B.∷ B.⟨ X† ⟩ B.⊢M⦂ Y†} →
                       M ~-tm-m M† →
                       N ~-tm-m N† →
                       ------------------------------------------
                       (promise op ∣ p ↦ M `in N) ~-tm-m (B.promise op ↦ M† `in N†)

  ~await_until_      : {X : VType} {X† : B.Type}
                       {C : CType} {C' : B.Type}
                       {V : Γ ⊢V⦂ ⟨ X ⟩} {V† : Γ† B.⊢V⦂ B.⟨ X† ⟩}
                       {M : Γ ∷ X ⊢M⦂ C} {M† : Γ† B.∷ X† B.⊢M⦂ C'} →
                       V ~-tm-v V† →
                       M ~-tm-m M† →
                       --------------
                       (await V until M) ~-tm-m (B.await V† until M†)

  ~coerce            : {X : VType} {X† : B.Type}
                       {o o' : O}
                       {i i' : I}
                       (r : o ⊑ₒ o')
                       (q : i ⊑ᵢ i')
                       {M : Γ ⊢M⦂ X ! (o , i)} {M† : Γ† B.⊢M⦂ X†} →
                       M ~-tm-m M† →
                       -------------------
                       (coerce r q M) ~-tm-m (B.coerce M†)

data _~-ren_ : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx} → Ren Γ Δ → B.Ren Γ† Δ† → Set where
  ~-ren-cons : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
               {rn : Ren Γ Δ} {rn† : B.Ren Γ† Δ†} →
               Γ ~-ctx Γ† →
               Δ ~-ctx Δ† →
               ({X : VType} {X† : B.Type}
                  {x : X ∈ Γ} {x† : X† B.∈ Γ†} →
                  x ~-∈ x† →
                  rn x ~-∈ rn† x†) →
               -----------------
               rn ~-ren rn†

data _~-sub_ : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx} → Sub Γ Δ → B.Sub Γ† Δ† → Set where
  ~-sub-cons : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
               {s : Sub Γ Δ} {s† : B.Sub Γ† Δ†} →
               Γ ~-ctx Γ† →
               Δ ~-ctx Δ† →
               ({X : VType} {X† : B.Type}
                  {x : X ∈ Γ} {x† : X† B.∈ Γ†} →
                  x ~-∈ x† →
                  s x ~-tm-v s† x†) →
               -----------------
               s ~-sub s†

~-ctx-∈ : {Γ : Ctx} {Γ† : B.Ctx}
          {X : VType} {X† : B.Type} →
          {x : X ∈ Γ} {x† : X† B.∈ Γ†} →
          x ~-∈ x† →
          ----------------
          Γ ~-ctx Γ†
~-ctx-∈ (~Hd ~x ~X) = ~x ~∷ ~X
~-ctx-∈ (~Tl ~x ~X) = ~-ctx-∈ ~x ~∷ ~X

~-ctx-tm-v : {Γ : Ctx} {Γ† : B.Ctx}
             {X : VType} {X† : B.Type}
             {V : Γ ⊢V⦂ X} {V† : Γ† B.⊢V⦂ X†} →
             V ~-tm-v V† →
             ----------------
             Γ ~-ctx Γ†

~-ctx-tm-m : {Γ : Ctx} {Γ† : B.Ctx}
             {X : CType} {X† : B.Type}
             {M : Γ ⊢M⦂ X} {M† : Γ† B.⊢M⦂ X†} →
             M ~-tm-m M† →
             ----------------
             Γ ~-ctx Γ†

~-ctx-tm-v (~` ~x) = ~-ctx-∈ ~x
~-ctx-tm-v (~``_ {~Γ} c) = ~Γ
~-ctx-tm-v (~ƛ ~M) with ~-ctx-tm-m ~M
... | ~Γ ~∷ _ = ~Γ
~-ctx-tm-v ~⟨ ~V ⟩ = ~-ctx-tm-v ~V

~-ctx-tm-m (~return ~V) = ~-ctx-tm-v ~V
~-ctx-tm-m (~let= _ `in ~N) with ~-ctx-tm-m ~N
... | ~Γ ~∷ _ = ~Γ
~-ctx-tm-m (~V ~· _) = ~-ctx-tm-v ~V
~-ctx-tm-m (~↑ _ _ _ ~M) = ~-ctx-tm-m ~M
~-ctx-tm-m (~↓ _ _ ~M) = ~-ctx-tm-m ~M
~-ctx-tm-m (~promise _ ∣ _ ↦ _ `in ~N) with ~-ctx-tm-m ~N
... | ~Γ ~∷ _ = ~Γ
~-ctx-tm-m (~await _ until ~M) with ~-ctx-tm-m ~M
... | ~Γ ~∷ _ = ~Γ
~-ctx-tm-m (~coerce _ _ ~M) = ~-ctx-tm-m ~M

~-ty-∈ : {Γ : Ctx} {Γ† : B.Ctx}
         {X : VType} {X† : B.Type}
         {x : X ∈ Γ} {x† : X† B.∈ Γ†} →
         x ~-∈ x† →
         ----------------
         X ~-ty-v X†
~-ty-∈ (~Hd _ ~X) = ~X
~-ty-∈ (~Tl ~x _) = ~-ty-∈ ~x

~-ty-tm-v : {Γ : Ctx} {Γ† : B.Ctx}
            {X : VType} {X† : B.Type}
            {V : Γ ⊢V⦂ X} {V† : Γ† B.⊢V⦂ X†} →
            V ~-tm-v V† →
            ----------------
            X ~-ty-v X† 

~-ty-tm-m : {Γ : Ctx} {Γ† : B.Ctx}
            {X : CType} {X† : B.Type}
            {M : Γ ⊢M⦂ X} {M† : Γ† B.⊢M⦂ X†} →
            M ~-tm-m M† →
            ----------------
            X ~-ty-m X† 

~-ty-tm-v (~` ~x) = ~-ty-∈ ~x
~-ty-tm-v (~`` c) = ~``` (ar-base c)
~-ty-tm-v (~ƛ ~M) with ~-ctx-tm-m ~M
... | _ ~∷ ~X = ~X ~⇒ (~-ty-tm-m ~M)
~-ty-tm-v ~⟨ ~V ⟩ = ~⟨ ~-ty-tm-v ~V ⟩

~-ty-tm-m (~return ~V) = ~! (~-ty-tm-v ~V)
~-ty-tm-m (~let= ~M `in ~N) = ~-ty-tm-m ~N
~-ty-tm-m (~V ~· ~W) with ~-ty-tm-v ~V
... | _ ~⇒ ~X = ~X
~-ty-tm-m (~↑ _ _ _ ~M) = ~-ty-tm-m ~M
~-ty-tm-m (~↓ _ _ ~M) with ~-ty-tm-m ~M
... | ~! ~X = ~! ~X
~-ty-tm-m (~promise _ ∣ _ ↦ _ `in ~N) = ~-ty-tm-m ~N
~-ty-tm-m (~await _ until ~M) = ~-ty-tm-m ~M
~-ty-tm-m (~coerce _ _ ~M) with ~-ty-tm-m ~M
... | ~! ~X = ~! ~X

~-ty-m-v : {X : VType} {X† : B.Type}
           {o : O} {i : I} →
           (X ! (o , i)) ~-ty-m X† →
           ---------------
           X ~-ty-v X†
~-ty-m-v (~! ~X) = ~X

~-wk₂ : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
        {X : VType} {X† : B.Type}
        {rn : Ren Γ Δ} {rn† : B.Ren Γ† Δ†} →
        X ~-ty-v X† →
        rn ~-ren rn† →
        wk₂ {X = X} rn ~-ren B.wk₂ {X = X†} rn†
~-wk₂ ~X (~-ren-cons ~Γ ~Δ f) =
  ~-ren-cons (~Γ ~∷ ~X) (~Δ ~∷ ~X) (λ {(~Hd _ _) → ~Hd ~Δ ~X; (~Tl ~x ~Y) → ~Tl (f ~x) ~Y})

~-rn-v : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
         {X : VType} {X† : B.Type}
         {V : Γ ⊢V⦂ X} {V† : Γ† B.⊢V⦂ X†}
         {rn : Ren Γ Δ} {rn† : B.Ren Γ† Δ†} →
         V ~-tm-v V† →
         rn ~-ren rn† →
         ------------------------------------------
         V-rename rn V ~-tm-v B.V-rename rn† V†

~-rn-m : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
         {X : CType} {X† : B.Type}
         {M : Γ ⊢M⦂ X} {M† : Γ† B.⊢M⦂ X†}
         {rn : Ren Γ Δ} {rn† : B.Ren Γ† Δ†} →
         M ~-tm-m M† →
         rn ~-ren rn† →
         ------------------------------------------
         M-rename rn M ~-tm-m B.M-rename rn† M†

~-rn-lift : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
            {X : VType} {X† : B.Type}
            {Y : CType} {Y† : B.Type}
            {rn : Ren Γ Δ} {rn† : B.Ren Γ† Δ†} →
            {M : Γ ∷ X ⊢M⦂ Y} {M† : Γ† B.∷ X† B.⊢M⦂ Y†} →
            M ~-tm-m M† →
            rn ~-ren rn† →
            ------------------------------
            M-rename (wk₂ rn) M ~-tm-m B.M-rename (B.wk₂ rn†) M†
~-rn-lift ~M ~rn with ~-ctx-tm-m ~M
... | ~u ~∷ ~X = ~-rn-m ~M (~-wk₂ ~X ~rn)

~-rn-v (~` ~x) (~-ren-cons _ _ f) = ~` f ~x
~-rn-v (~`` c) (~-ren-cons _ ~Δ _) = ~``_ {x = ~Δ} c
~-rn-v (~ƛ ~M) ~rn = ~ƛ (~-rn-lift ~M ~rn)
~-rn-v (~⟨ ~V ⟩) ~rn = ~⟨ ~-rn-v ~V ~rn ⟩

~-rn-m (~return ~V) ~rn = ~return (~-rn-v ~V ~rn)
~-rn-m (~let= ~M `in ~N) ~rn = ~let= (~-rn-m ~M ~rn) `in (~-rn-lift ~N ~rn)
~-rn-m (~V ~· ~W) ~rn = (~-rn-v ~V ~rn) ~· ~-rn-v ~W ~rn
~-rn-m (~↑ op _ ~V ~M) ~rn = ~↑ op _ (~-rn-v ~V ~rn) (~-rn-m ~M ~rn)
~-rn-m (~↓ op ~V ~M) ~rn = ~↓ op (~-rn-v ~V ~rn) (~-rn-m ~M ~rn)
~-rn-m (~promise op ∣ _ ↦ ~M `in ~N) ~rn = ~promise op ∣ _ ↦ (~-rn-lift ~M ~rn) `in (~-rn-lift ~N ~rn)
~-rn-m (~await ~V until ~M) ~rn = ~await (~-rn-v ~V ~rn) until (~-rn-lift ~M ~rn)
~-rn-m (~coerce _ _ ~M) ~rn = ~coerce _ _ (~-rn-m ~M ~rn)

~-rn-wk₁ : {Γ : Ctx} {Γ† : B.Ctx}
           {X : VType} {X† : B.Type}
           {V : Γ ⊢V⦂ X} {V† : Γ† B.⊢V⦂ X†} →
           X ~-ty-v X† →
           V ~-tm-v V† →
           (V-rename (wk₁ {X = X}) V) ~-tm-v (B.V-rename (B.wk₁ {X = X†}) V†)
~-rn-wk₁ ~X ~V = ~-rn-v ~V (~-ren-cons (~-ctx-tm-v ~V) ((~-ctx-tm-v ~V) ~∷ ~X) (λ z → ~Tl z ~X))

~-lift : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
         {X : VType} {X† : B.Type} →
         {s : Sub Γ Δ} {s† : B.Sub Γ† Δ†} →
         X ~-ty-v X† →
         s ~-sub s† →
         lift {X = X} s ~-sub B.lift {X = X†} s†
~-lift ~X (~-sub-cons ~Γ ~Δ f)
  = ~-sub-cons (~Γ ~∷ ~X) (~Δ ~∷ ~X)
      (λ {(~Hd _ _) → ~` (~Hd ~Δ ~X); (~Tl ~x ~Y) → ~-rn-v (f ~x) (~-ren-cons ~Δ (~Δ ~∷ ~Y) (λ z → ~Tl z ~X))})

~-id-subst : {Γ : Ctx} {Γ† : B.Ctx}
             {X : VType} {X† : B.Type}
             {V : Γ ⊢V⦂ X} {V† : Γ† B.⊢V⦂ X†} →
             Γ ~-ctx Γ† →
             X ~-ty-v X† →
             V ~-tm-v V† →
             -----------------------
             (id-subst {Γ} [ V ]s) ~-sub (B.id-subst {Γ†} B.[ V† ]s)
~-id-subst ~Γ ~X ~V = ~-sub-cons (~Γ ~∷ ~X) ~Γ (λ {(~Hd _ _) → ~V; (~Tl ~x _) → ~` ~x})

~-sub-v : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
          {X : VType} {X† : B.Type}
          {V : Γ ⊢V⦂ X} {V† : Γ† B.⊢V⦂ X†}
          {s : Sub Γ Δ} {s† : B.Sub Γ† Δ†} →
          V ~-tm-v V† →
          s ~-sub s† →
          ----------------------------
          (V [ s ]v) ~-tm-v (V† B.[ s† ]v)

~-sub-m : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
          {X : CType} {X† : B.Type}
          {M : Γ ⊢M⦂ X} {M† : Γ† B.⊢M⦂ X†}
          {s : Sub Γ Δ} {s† : B.Sub Γ† Δ†} →
          M ~-tm-m M† →
          s ~-sub s† →
          ----------------------------
          (M [ s ]m) ~-tm-m (M† B.[ s† ]m)

~-sub-lift : {Γ Δ : Ctx} {Γ† Δ† : B.Ctx}
             {X : VType} {X† : B.Type}
             {Y : CType} {Y† : B.Type}
             {s : Sub Γ Δ} {s† : B.Sub Γ† Δ†} →
             {M : Γ ∷ X ⊢M⦂ Y} {M† : Γ† B.∷ X† B.⊢M⦂ Y†} →
             M ~-tm-m M† →
             s ~-sub s† →
             -----------------------------
             (M [ lift s ]m) ~-tm-m (M† B.[ B.lift s† ]m)
~-sub-lift ~M ~s with ~-ctx-tm-m ~M
... | _ ~∷ ~X = ~-sub-m ~M (~-lift ~X ~s)

~-sub-v (~` ~x) (~-sub-cons _ _ f) = f ~x
~-sub-v (~`` c) (~-sub-cons _ ~Δ _) = ~``_ {x = ~Δ} c
~-sub-v (~ƛ ~M) ~s = ~ƛ (~-sub-lift ~M ~s)
~-sub-v ~⟨ ~V ⟩ ~s = ~⟨ ~-sub-v ~V ~s ⟩

~-sub-m (~return ~V) ~s = ~return (~-sub-v ~V ~s)
~-sub-m (~let= ~M `in ~N) ~s = ~let= (~-sub-m ~M ~s) `in (~-sub-lift ~N ~s)
~-sub-m (~V ~· ~W) ~s = (~-sub-v ~V ~s) ~· (~-sub-v ~W ~s)
~-sub-m (~↑ op _ ~V ~M) ~s = ~↑ op _ (~-sub-v ~V ~s) (~-sub-m ~M ~s)
~-sub-m (~↓ op ~V ~M) ~s = ~↓ op (~-sub-v ~V ~s) (~-sub-m ~M ~s)
~-sub-m (~promise op ∣ _ ↦ ~M `in ~N) ~s = ~promise op ∣ _ ↦ (~-sub-lift ~M ~s) `in (~-sub-lift ~N ~s)
~-sub-m (~await ~V until ~M) ~s = ~await (~-sub-v ~V ~s) until (~-sub-lift ~M ~s)
~-sub-m (~coerce _ _ ~M) ~s = ~coerce _ _ (~-sub-m ~M ~s)

~-subst-v : {Γ : Ctx} {Γ† : B.Ctx}
            {X Y : VType} {X† Y† : B.Type}
            {V : (Γ ∷ X) ⊢V⦂ Y} {V† : (Γ† B.∷ X†) B.⊢V⦂ Y†}
            {W : Γ ⊢V⦂ X} {W† : Γ† B.⊢V⦂ X†} →
            V ~-tm-v V† →
            W ~-tm-v W† →
            ----------------------
            V [ id-subst [ W ]s ]v ~-tm-v V† B.[ B.id-subst B.[ W† ]s ]v
~-subst-v ~V ~W = ~-sub-v ~V (~-id-subst (~-ctx-tm-v ~W) (~-ty-tm-v ~W) ~W)

~-subst-m : {Γ : Ctx} {Γ† : B.Ctx}
            {X : VType} {X† : B.Type}
            {Y : CType} {Y† : B.Type}
            {M : (Γ ∷ X) ⊢M⦂ Y} {M† : (Γ† B.∷ X†) B.⊢M⦂ Y†}
            {V : Γ ⊢V⦂ X} {V† : Γ† B.⊢V⦂ X†} →
            M ~-tm-m M† →
            V ~-tm-v V† →
            ----------------------
            M [ id-subst [ V ]s ]m ~-tm-m M† B.[ B.id-subst B.[ V† ]s ]m
~-subst-m ~M ~V = ~-sub-m ~M (~-id-subst (~-ctx-tm-v ~V) (~-ty-tm-v ~V) ~V)

~-bctx-⋈ : {Γ : Ctx} {Γ† : B.Ctx}
           {Δ : BCtx} {Δ† : B.BCtx} →
           Δ ~-bctx Δ† →
           (Γ ⋈ Δ) ~-ctx (Γ† B.⋈ Δ†) →
           -----------------------
           Γ ~-ctx Γ†
~-bctx-⋈ ~[] ~Γ = ~Γ
~-bctx-⋈ (~X ~∷ ~Δ) ~Γ with ~-bctx-⋈ ~Δ ~Γ
... | ~Γ ~∷ _ = ~Γ

~-strengthen-var : {Γ : Ctx} {Γ† : B.Ctx}
                   {Δ : BCtx} {Δ† : B.BCtx}
                   {A : BType}
                   {x : ``` A ∈ Γ ⋈ Δ} {x† : B.``` A B.∈ Γ† B.⋈ Δ†} →
                   Δ ~-bctx Δ† →
                   x ~-∈ x† →
                   --------------------------
                   (strengthen-var Δ x) ~-∈ (B.strengthen-var Δ† x†)
~-strengthen-var ~[] ~x = ~x
~-strengthen-var {Δ = X ∷ₗ Δ} {Δ† = X† ∷ₗ Δ†} {x = x} {x† = x†} (~X ~∷ ~Δ) ~x
  with strengthen-var Δ x | B.strengthen-var Δ† x† | ~-strengthen-var ~Δ ~x
...  | Tl _ | B.Tl _ | ~Tl ~x _ = ~x

~-strengthen-val : {Γ : Ctx} {Γ† : B.Ctx}
                   {Δ : BCtx} {Δ† : B.BCtx}
                   {A : BType}
                   {V : Γ ⋈ Δ ⊢V⦂ ``` A} {V† : Γ† B.⋈ Δ† B.⊢V⦂ B.``` A} →
                   Δ ~-bctx Δ† →
                   V ~-tm-v V† →
                   (strengthen-val {Δ = Δ} V) ~-tm-v (B.strengthen-val {Δ = Δ†} V†)
~-strengthen-val ~Δ (~` ~x) = ~` ~-strengthen-var ~Δ ~x
~-strengthen-val ~Δ (~``_ {x = ~Γ} c) = ~``_ {x = ~-bctx-⋈ ~Δ ~Γ} c

incl-ty-v : (X : VType) → Σ[ X† ∈ B.Type ] X ~-ty-v X†

incl-ty-m : (X : CType) → Σ[ X† ∈ B.Type ] X ~-ty-m X†

incl-ty-v (``` x) = B.``` x , ~``` x
incl-ty-v (X ⇒ Y) with incl-ty-v X | incl-ty-m Y
... | X† , ~X | Y† , ~Y = X† B.⇒ Y† , (~X ~⇒ ~Y)
incl-ty-v ⟨ X ⟩ with incl-ty-v X
... | X† , ~X = B.⟨ X† ⟩ , ~⟨ ~X ⟩

incl-ty-m (X ! _) with incl-ty-v X
... | X† , ~X = X† , ~! ~X

uniq-ty-v : {X : VType} {X† X†' : B.Type} →
            X ~-ty-v X† →
            X ~-ty-v X†' →
            ---------------
            X† ≡ X†'
uniq-ty-v (~``` ~x) (~``` .~x) = refl
uniq-ty-v (~X ~⇒ ~! ~Y) (~X† ~⇒ ~! ~Y†) = cong₂ B._⇒_ (uniq-ty-v ~X ~X†) (uniq-ty-v ~Y ~Y†)
uniq-ty-v ~⟨ ~X ⟩ ~⟨ ~X† ⟩ = cong B.⟨_⟩ (uniq-ty-v ~X ~X†)

incl-ctx : (Γ : Ctx) → Σ[ Γ† ∈ B.Ctx ] Γ ~-ctx Γ†
incl-ctx ([]) = B.[] , ~[]
incl-ctx (Γ ∷ X) with incl-ctx Γ | incl-ty-v X
... | Γ† , ~Γ | X† , ~X = Γ† B.∷ X† , (~Γ ~∷ ~X)

incl-∈ : {Γ : Ctx} {Γ† : B.Ctx}
         {X : VType} {X† : B.Type} →
         Γ ~-ctx Γ† →
         X ~-ty-v X† →
         (x : X ∈ Γ) →
         -----------------------
         Σ[ x† ∈ X† B.∈ Γ† ] x ~-∈ x†
incl-∈ (~Γ ~∷ ~Y) ~X Hd rewrite uniq-ty-v ~X ~Y = B.Hd , ~Hd ~Γ ~Y
incl-∈ (~Γ ~∷ ~Y) ~X (Tl x) with incl-∈ ~Γ ~X x
... | x† , ~x = B.Tl x† , ~Tl ~x ~Y

incl-tm-v : {Γ : Ctx} {Γ† : B.Ctx}
            {X : VType} {X† : B.Type} →
            Γ ~-ctx Γ† →
            X ~-ty-v X† →
            (V : Γ ⊢V⦂ X) →
            ---------------------
            Σ[ V† ∈ Γ† B.⊢V⦂ X† ] V ~-tm-v V†

incl-tm-m : {Γ : Ctx} {Γ† : B.Ctx}
            {X : CType} {X† : B.Type} →
            Γ ~-ctx Γ† →
            X ~-ty-m X† →
            (M : Γ ⊢M⦂ X) →
            ---------------------
            Σ[ M† ∈ Γ† B.⊢M⦂ X† ] M ~-tm-m M†

incl-tm-v ~Γ ~X (` x) with incl-∈ ~Γ ~X x
... | x† , ~x = (B.` x†) , ~` ~x
incl-tm-v ~Γ (~``` _) (``_ c) = B.`` c , (~``_ {x = ~Γ} c)
incl-tm-v ~Γ (~X ~⇒ ~Y) (ƛ M) with incl-tm-m (~Γ ~∷ ~X) ~Y M
... | M† , ~M = B.ƛ M† , ~ƛ ~M
incl-tm-v ~Γ ~⟨ ~X ⟩ ⟨ V ⟩ with incl-tm-v ~Γ ~X V
... | V† , ~V = B.⟨ V† ⟩ , ~⟨ ~V ⟩

incl-tm-m ~Γ (~! ~X) (return V) with incl-tm-v ~Γ ~X V
... | V† , ~V = B.return V† , ~return ~V
incl-tm-m ~Γ ~X (let=_`in_ {Y} M N) with incl-ty-v Y
... | Y† , ~Y with incl-tm-m ~Γ (~! ~Y) M | incl-tm-m (~Γ ~∷ ~Y) ~X N
...   | M† , ~M | N† , ~N = B.let= M† `in N† , ~let= ~M `in ~N
incl-tm-m ~Γ ~X (_·_ {Y} V W) with incl-ty-v Y
... | Y† , ~Y with incl-tm-v ~Γ (~Y ~⇒ ~X) V | incl-tm-v ~Γ ~Y W
...   | V† , ~V | W† , ~W = V† B.· W† , ~V ~· ~W
incl-tm-m ~Γ ~X (↑ op _ V M) with incl-tm-v ~Γ (~``` (payload op)) V | incl-tm-m ~Γ ~X M
... | V† , ~V | M† , ~M = B.↑ op V† M† , ~↑ op _ ~V ~M
incl-tm-m ~Γ (~! ~X) (↓ op V M) with incl-tm-v ~Γ (~``` (payload op)) V | incl-tm-m ~Γ (~! ~X) M
... | V† , ~V | M† , ~M = B.↓ op V† M† , ~↓ op ~V ~M
incl-tm-m ~Γ ~X (promise_∣_↦_`in_ {Y} op _ M N) with incl-ty-v Y
... | Y† , ~Y with incl-tm-m (~Γ ~∷ ~``` (payload op)) (~! ~⟨ ~Y ⟩) M | incl-tm-m (~Γ ~∷ ~⟨ ~Y ⟩) ~X N
...   | M† , ~M | N† , ~N = B.promise op ↦ M† `in N† , ~promise op ∣ _ ↦ ~M `in ~N
incl-tm-m ~Γ ~X (await_until_ {Y} V M) with incl-ty-v Y
... | Y† , ~Y with incl-tm-v ~Γ ~⟨ ~Y ⟩ V | incl-tm-m (~Γ ~∷ ~Y) ~X M
...   | V† , ~V | M† , ~M = B.await V† until M† , ~await ~V until ~M
incl-tm-m ~Γ (~! ~X) (coerce _ _ M) with incl-tm-m ~Γ (~! ~X) M
... | M† , ~M = B.coerce M† , ~coerce _ _ ~M

incl-tm-v' : {Γ : Ctx} {X : VType} (V : Γ ⊢V⦂ X) →
             ---------------------
             Σ[ Γ† ∈ B.Ctx ] Σ[ X† ∈ B.Type ] Σ[ V† ∈ Γ† B.⊢V⦂ X† ] V ~-tm-v V†
incl-tm-v' {Γ} {X} V with incl-ctx Γ | incl-ty-v X
... | Γ† , ~Γ | X† , ~X with incl-tm-v ~Γ ~X V
...   | V† , ~V = Γ† , X† , V† , ~V

incl-tm-m' : {Γ : Ctx} {X : CType} (M : Γ ⊢M⦂ X) →
             ---------------------
             Σ[ Γ† ∈ B.Ctx ] Σ[ X† ∈ B.Type ] Σ[ M† ∈ Γ† B.⊢M⦂ X† ] M ~-tm-m M†
incl-tm-m' {Γ} {X} M with incl-ctx Γ | incl-ty-m X
... | Γ† , ~Γ | X† , ~X with incl-tm-m ~Γ ~X M
...   | M† , ~M = Γ† , X† , M† , ~M

data Leg {Γ : Ctx} {Γ† : B.Ctx} {X : CType} {X† : B.Type} (M† : Γ† B.⊢M⦂ X†) (N : Γ ⊢M⦂ X) : Set where
  leg : {N† : Γ† B.⊢M⦂ X†} →
        N ~-tm-m N† →
        M† B.↝↝ N† →
        ----------------
        Leg M† N

sim : {Γ : Ctx} {Γ† : B.Ctx}
      {X : CType} {X† : B.Type}
      {M N : Γ ⊢M⦂ X} →
      {M† : Γ† B.⊢M⦂ X†} →
      M ↝↝ N →
      M ~-tm-m M† →
      -------------------
      Leg M† N
sim (apply _ _) (~ƛ ~M ~· ~W)
  = leg (~-subst-m ~M ~W) (B.apply _ _)
sim (let-return _ _) (~let= ~return ~V `in ~N)
  = leg (~-subst-m ~N ~V) (B.let-return _ _)
sim (let-↑ _ _ _ _) (~let= ~↑ op _ ~V ~M `in ~N) = leg (~↑ op _ ~V (~let= ~M `in ~N)) (B.let-↑ _ _ _)
sim (let-promise _ _ _ _) (~let= ~promise op ∣ _ ↦ ~M `in ~N `in ~L)
  = leg (~promise op ∣ _ ↦ ~M `in (~let= ~N `in (~-rn-m ~L (~-ren-cons (~-ctx-tm-m ~L) (~-ctx-tm-m ~N ~∷ (~-ty-m-v (~-ty-tm-m ~N)))
        (λ {(~Hd _ ~X) → ~Hd (~-ctx-tm-m ~N) ~X; (~Tl ~x ~X) → ~Tl (~Tl ~x (~-ty-m-v (~-ty-tm-m ~M))) ~X}))))) (B.let-promise _ _ _)
sim (promise-↑ _ _ _ _ _) (~promise op ∣ _ ↦ ~M `in (~↑ op' _ ~V ~N)) with ~-ty-tm-m ~M
... | (~! ~⟨ ~X ⟩) = leg (~↑ op' _ (~-strengthen-val (~X ~∷ ~[]) ~V) (~promise op ∣ _ ↦ ~M `in ~N)) (B.promise-↑ _ _ _)
sim (↓-return _ _) (~↓ op ~V (~return ~W)) = leg (~return ~W) (B.↓-return _ _)
sim (↓-↑ _ _ _ _) (~↓ op ~V (~↑ op' _ ~W ~M)) = leg (~↑ op' _ ~W (~↓ op ~V ~M)) (B.↓-↑ _ _ _)
sim (↓-promise-op _ _ _ _) (~↓ op ~V (~promise op ∣ _ ↦ ~M `in ~N))
  = leg
      (~let= (~coerce _ _ (~-subst-m ~M ~V)) `in
          ~↓ op (~-rn-v ~V (~-ren-cons (~-ctx-tm-v ~V) (~-ctx-tm-m ~N) (λ z → ~Tl z (~-ty-m-v (~-ty-tm-m ~M)))))
          (~-sub-m
            (~-rn-m ~N
              (~-ren-cons (~-ctx-tm-m ~N) (~-ctx-tm-m ~N ~∷ (~-ty-m-v (~-ty-tm-m ~M)))
                (λ {(~Hd ~x ~X) → ~Hd (~x ~∷ ~X) ~X; (~Tl ~x ~X) → ~Tl (~Tl ~x ~X) ~X})))
              (~-id-subst (~-ctx-tm-m ~N) ((~-ty-m-v (~-ty-tm-m ~M))) (~` (~Hd (~-ctx-tm-v ~V) (~-ty-m-v (~-ty-tm-m ~M)))))))
      (B.↓-promise-op _ _ _)
sim (↓-promise-op' p _ _ _ _) (~↓ op ~V (~promise op' ∣ _ ↦ ~M `in ~N))
  = leg
     (~promise op' ∣ _ ↦ (~coerce _ _ ~M) `in
         ~↓ op ((~-rn-v ~V (~-ren-cons (~-ctx-tm-v ~V) (~-ctx-tm-m ~N) (λ z → ~Tl z (~-ty-m-v (~-ty-tm-m ~M)))))) ~N)
     (B.↓-promise-op' p _ _ _)
sim (await-promise _ _) (~await ~⟨ ~V ⟩ until ~N) = leg (~-subst-m ~N ~V) (B.await-promise _ _)
sim (context-let r) (~let= ~M `in ~N) with sim r ~M
... | leg ~M r' = leg (~let= ~M `in ~N) (B.context-let r')
sim (context-↑ r) (~↑ op _ ~V ~M) with sim r ~M
... | leg ~M r' = leg (~↑ op _ ~V ~M) (B.context-↑ r')
sim (context-↓ r) (~↓ op ~V ~M) with sim r ~M
... | leg ~M r' = leg (~↓ op ~V ~M) (B.context-↓ r')
sim (context-promise r) (~promise op ∣ _ ↦ ~M `in ~N) with sim r ~N
... | leg ~N r' = leg (~promise op ∣ _ ↦ ~M `in ~N) (B.context-promise r')
sim (context-coerce r) (~coerce _ _ ~N) with sim r ~N
... | leg ~N r' = leg (~coerce _ _ ~N) (B.context-coerce r')
sim (coerce-return _) (~coerce _ _ (~return ~V))
  = leg (~return ~V) (B.coerce-return _)
sim (coerce-↑ _ _ _) (~coerce _ _ (~↑ op _ ~V ~N))
  = leg (~↑ op _ ~V (~coerce _ _ ~N)) (B.coerce-↑ _ _)
sim (coerce-promise _ _ _) (~coerce _ _ (~promise op ∣ _ ↦ ~M `in ~N))
  = leg (~promise op ∣ _ ↦ ~coerce _ _ ~M `in ~coerce _ _ ~N) (B.coerce-promise _ _)

data SN : {Γ : Ctx} {X : CType} → Γ ⊢M⦂ X → Set where
  sn : {Γ : Ctx}
       {X : CType}
       {M : Γ ⊢M⦂ X} →
       ({N : Γ ⊢M⦂ X} → M ↝↝ N → SN N) →
       --------------------------------
       SN M

sn'→sn : {Γ : Ctx} {Γ† : B.Ctx}
         {X : CType} {X† : B.Type}
         {M N : Γ ⊢M⦂ X} {M† : Γ† B.⊢M⦂ X†} →
         M ~-tm-m M† →
         SN' M† →
         M ↝↝ N →
         -------------------
         SN N
sn'→sn ~M (sn f) r with sim r ~M
... | leg ~N r' = sn (sn'→sn ~N (f r'))

{- COROLLARY 3.18 -}

all-terms-sn : {Γ : Ctx} {X : CType} (M : Γ ⊢M⦂ X) → SN M
all-terms-sn M with incl-tm-m' M
... | _ , _ , M† , ~M = sn (sn'→sn ~M (all-terms-sn' M†))