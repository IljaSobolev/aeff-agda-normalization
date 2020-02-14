open import Data.List renaming (_∷_ to _∷∷_ ; [_] to ⟦_⟧)
open import Data.Maybe
open import Data.Product
open import Data.Sum

open import Calculus
open import EffectAnnotations
open import Preservation
open import ProcessCalculus
open import ProcessTypes
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module ProcessPreservation where

-- WELL-TYPED SIGNAL HOISTING CONTEXTS

data _⊢H[_]⦂_ (Γ : Ctx) : (Δ : BCtx) → CType → Set where

  [-]              : {C : CType} →
                     -------------
                     Γ ⊢H[ [] ]⦂ C

  promise_∣_↦_`in_ : {Δ : BCtx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (op : Σₙ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ ``(arₙ op) ⊢M⦂ X ! (o' , i') →
                     Γ ∷ ⟨ X ⟩ ⊢H[ Δ ]⦂ Y ! (o , i) →
                     ----------------------------------
                     Γ ⊢H[ X ∷∷ Δ ]⦂ Y ! (o , i)

  subsume          : {Δ : BCtx}
                     {X : VType}
                     {o o' : O}
                     {i i' : I} →
                     o ⊑ₒ o' →
                     i ⊑ᵢ i' → 
                     Γ ⊢H[ Δ ]⦂ X ! (o , i) →
                     ------------------------
                     Γ ⊢H[ Δ ]⦂ X ! (o' , i')


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED SIGNAL HOISTING CONTEXT

hole-ty-hₒ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
             Γ ⊢H[ Δ ]⦂ X ! (o , i) → O
hole-ty-hₒ {_} {_} {_} {o} [-] =
  o
hole-ty-hₒ (promise op ∣ p ↦ M `in H) =
  hole-ty-hₒ H
hole-ty-hₒ (subsume p q H) =
  hole-ty-hₒ H


hole-ty-hᵢ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
             Γ ⊢H[ Δ ]⦂ X ! (o , i) → I
hole-ty-hᵢ {_} {_} {_} {_} {o} [-] =
  o
hole-ty-hᵢ (promise op ∣ p ↦ M `in H) =
  hole-ty-hᵢ H
hole-ty-hᵢ (subsume p q H) =
  hole-ty-hᵢ H


hole-ty-h-⊑ₒ : {Γ : Ctx}
             {Δ : BCtx}
             {X : VType}
             {o : O}
             {i : I} →
             (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) →
             ------------------------------
             hole-ty-hₒ H ⊑ₒ o
hole-ty-h-⊑ₒ [-] =
  ⊑ₒ-refl
hole-ty-h-⊑ₒ (promise op ∣ p ↦ M `in H) =
  hole-ty-h-⊑ₒ H
hole-ty-h-⊑ₒ (subsume p q H) =
  ⊑ₒ-trans (hole-ty-h-⊑ₒ H) p


hole-ty-h-⊑ᵢ : {Γ : Ctx}
             {Δ : BCtx}
             {X : VType}
             {o : O}
             {i : I} →
             (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) →
             ------------------------------
             hole-ty-hᵢ H ⊑ᵢ i
hole-ty-h-⊑ᵢ [-] =
  ⊑ᵢ-refl
hole-ty-h-⊑ᵢ (promise op ∣ p ↦ M `in H) =
  hole-ty-h-⊑ᵢ H
hole-ty-h-⊑ᵢ (subsume p q H) =
  ⊑ᵢ-trans (hole-ty-h-⊑ᵢ H) q


-- FILLING A WELL-TYPED SIGNAL HOISTING CONTEXT

infix 30 _[_]ₕ

_[_]ₕ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
        (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) → Γ ⋈ Δ ⊢M⦂ (X ! (hole-ty-hₒ H , hole-ty-hᵢ H)) →
        Γ ⊢M⦂ X ! (o , i)
[-] [ M ]ₕ =
  M
(promise op ∣ p ↦ N `in E) [ M ]ₕ =
  promise op ∣ p ↦ N `in (E [ M ]ₕ)
subsume p q E [ M ]ₕ =
  subsume p q (E [ M ]ₕ)


-- EVOLUTION OF PROCESS TYPES

infix 10 _⇝_

data _⇝_ : {o o' : O} → PType o → PType o' → Set where

  id  : {X : VType}
        {o : O}
        {i : I} → 
        ----------------------
        X ‼ o , i ⇝ X ‼ o , i

  act : {X : VType}
        {o o' o'' : O}
        {i i' i'' : I} →
        (ops : List Σₙ) →
        (op : Σₙ) →   
        (o' , i') ≡ ops ↓↓ₑ (o , i) →
        (o'' , i'') ≡ ((ops ++ ⟦ op ⟧) ↓↓ₑ (o , i)) → 
        ---------------------------------------------
        (X ‼ o' , i') ⇝ (X ‼ o'' , i'')

  par : {o o' o'' o''' : O}
        {PP : PType o}
        {QQ : PType o'}
        {PP' : PType o''}
        {QQ' : PType o'''} → 
        PP ⇝ PP' →
        QQ ⇝ QQ' →
        ----------------------
        (PP ∥ QQ) ⇝ (PP' ∥ QQ')


-- EVOLUTION OF PROCESS TYPES IS REFLEXIVE

⇝-refl : {o : O} {PP : PType o} → PP ⇝ PP
⇝-refl {o} {X ‼ o , i} =
  id
⇝-refl {.(_ ∪ₒ _)} {PP ∥ QQ} =
  par ⇝-refl ⇝-refl


-- ACTION OF INTERRUPTS ON GENERAL PROCESS TYPES IS AN EVOLUTION

⇝-↓ : {o : O}
      {PP : PType o}
      {op : Σₙ} →
      --------------
      PP ⇝ op ↓ₚ PP

⇝-↓ {.o} {X ‼ o , i} {op} =
  act [] op refl refl
⇝-↓ {.(_ ∪ₒ _)} {PP ∥ QQ} {op} =
  par ⇝-↓ ⇝-↓


-- ACTION OF INTERRUPTS PRESERVES PROCESS TYPE EVOLUTION

⇝-↓ₚ : {o o' : O}
       {PP : PType o}
       {QQ : PType o'}
       {op : Σₙ} →
       PP ⇝ QQ → 
       --------------------
       op ↓ₚ PP ⇝ op ↓ₚ QQ

⇝-↓ₚ id =
  id
⇝-↓ₚ {_} {_} {_} {_} {op} (act {_} {o} {o'} {o''} {i} {i'} {i''} ops op' p q) =
  act {o = o} {i = i} (op ∷∷ ops) op' (cong (λ oi → op ↓ₑ oi) p) (cong (λ oi → op ↓ₑ oi) q) 
⇝-↓ₚ (par p q) =
  par (⇝-↓ₚ p) (⇝-↓ₚ q)


-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-var : {Γ : Ctx} → (Δ : BCtx) → {A : BType} → `` A ∈ Γ ⋈ Δ → `` A ∈ Γ
strengthen-var [] x = x
strengthen-var (y ∷∷ Δ) x with strengthen-var Δ x
... | Tl p = p


strengthen-val : {Γ : Ctx} {Δ : BCtx} {A : BType} → Γ ⋈ Δ ⊢V⦂ `` A → Γ ⊢V⦂ `` A
strengthen-val {_} {Δ} (` x) =
  ` strengthen-var Δ x
strengthen-val (``_ c) =
  ``_ c


-- EVALUATION CONTEXTS FOR PROCESSES

infix 10 _⊢F⦂_

data _⊢F⦂_ (Γ : Ctx) : {o : O} → PType o → Set where

  [-]     : {o : O} → 
            {PP : PType o} →
            --------------
            Γ ⊢F⦂ PP

  _∥ₗ_    : {o o' : O}
            {PP : PType o}
            {QQ : PType o'} → 
            Γ ⊢F⦂ PP →
            Γ ⊢P⦂ QQ →
            ------------------
            Γ ⊢F⦂ (PP ∥ QQ)

  _∥ᵣ_    : {o o' : O}
            {PP : PType o}
            {QQ : PType o'} →
            Γ ⊢P⦂ PP →
            Γ ⊢F⦂ QQ →
            ------------------
            Γ ⊢F⦂ (PP ∥ QQ)

  ↑       : {o : O}
            {PP : PType o}  →
            (op : Σₙ) →
            op ∈ₒ o →
            Γ ⊢V⦂ ``(arₙ op) →
            Γ ⊢F⦂ PP →
            ------------------
            Γ ⊢F⦂ PP

  ↓       : {o : O}
            {PP : PType o}
            (op : Σₙ) →
            Γ ⊢V⦂ ``(arₙ op) →
            Γ ⊢F⦂ PP →
            ------------------
            Γ ⊢F⦂ op ↓ₚ PP
            

-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED PROCESS EVALUATION CONTEXT

hole-ty-f : {Γ : Ctx} {o : O} {PP : PType o} → Γ ⊢F⦂ PP → Σ[ o' ∈ O ] (PType o')
hole-ty-f {_} {o} {PP} [-] =
  o , PP
hole-ty-f (_∥ₗ_ {o} {o'} {PP} {QQ} F Q) =
  (proj₁ (hole-ty-f F)) , proj₂ (hole-ty-f F)
hole-ty-f (_∥ᵣ_ {o} {o'} {PP} {QQ} P F) =
  (proj₁ (hole-ty-f F)) , proj₂ (hole-ty-f F)
hole-ty-f (↑ op p V F) =
  (proj₁ (hole-ty-f F)) , proj₂ (hole-ty-f F)
hole-ty-f (↓ op V F) =
  (proj₁ (hole-ty-f F)) , proj₂ (hole-ty-f F)


-- FILLING A WELL-TYPED PROCESS EVALUATION CONTEXT

infix 30 _[_]f

_[_]f : {Γ : Ctx} {o : O} {PP : PType o} → (F : Γ ⊢F⦂ PP) → (P : Γ ⊢P⦂ proj₂ (hole-ty-f F)) → Γ ⊢P⦂ PP
[-] [ P ]f =
  P
(F ∥ₗ Q) [ P ]f =
  (F [ P ]f) ∥ Q
(Q ∥ᵣ F) [ P ]f =
  Q ∥ (F [ P ]f)
(↑ op p V F) [ P ]f =
  ↑ op p V (F [ P ]f)
(↓ op V F) [ P ]f =
  ↓ op V (F [ P ]f)


-- TYPES OF WELL-TYPED PROCESS EVALUATION CONTEXTS ALSO EVOLVE

⇝-f-⇝ : {Γ : Ctx}
        {o o' : O}
        {PP : PType o}
        {QQ : PType o'} →
        (F : Γ ⊢F⦂ PP) →
        proj₂ (hole-ty-f F) ⇝ QQ →
        ------------------------------------------
        Σ[ o'' ∈ O ] Σ[ RR ∈ PType o'' ] (PP ⇝ RR)

⇝-f-⇝ = {!!}

{-
⇝-f-⇝ {_} {_} {QQ} [-] p =
  QQ , p
⇝-f-⇝ (_∥ₗ_ {_} {QQ} {o} F Q) p with ⇝-f-⇝ F p
... | ((RR ‼ o') , r) =
  ((RR ∥ QQ) ‼ (o' ∪ₒ o)) , par r ⇝-refl
⇝-f-⇝ (_∥ᵣ_ {PP} {_} {o} P F) p with ⇝-f-⇝ F p
... | ((RR ‼ o') , r) =
  ((PP ∥ RR) ‼ (o ∪ₒ o')) , par ⇝-refl r
⇝-f-⇝ (↑ op p V F) q with ⇝-f-⇝ F q
... | ((RR ‼ o') , r) =
  (RR ‼ o') , r
⇝-f-⇝ (↓ op V F) p with ⇝-f-⇝ F p
... | ((RR ‼ o') , r) =
  (proj₁ (op ↓ₚ (RR , o')) ‼ proj₂ (op ↓ₚ (RR , o'))) , ⇝-↓ₚ r
⇝-f-⇝ (subsume p q F) r with ⇝-f-⇝ F r
... | ((RR ‼ o') , s) =
  (RR ‼ o') , sub s p ⊑ₚ-refl q ⊑ₒ-refl


⇝-f : {Γ : Ctx}
      {PP QQ : PType} →
      (F : Γ ⊢F⦂ PP) →
      (p : hole-ty-f F ⇝ QQ) →
      --------------------------
      Γ ⊢F⦂ (proj₁ (⇝-f-⇝ F p))
      
⇝-f [-] p =
  [-]
⇝-f (F ∥ₗ Q) p with ⇝-f-⇝ F p | ⇝-f F p
... | ((RR ‼ o') , r) | F' =
  subsume ⊑ₚ-refl ∪ₒ-inl F' ∥ₗ subsume ⊑ₚ-refl ∪ₒ-inr Q
⇝-f (P ∥ᵣ F) p with ⇝-f-⇝ F p | ⇝-f F p
... | ((RR ‼ o') , r) | F' =
  subsume ⊑ₚ-refl ∪ₒ-inl P ∥ᵣ subsume ⊑ₚ-refl ∪ₒ-inr F'
⇝-f (↑ op p V F) q with ⇝-f-⇝ F q | ⇝-f F q
... | ((RR ‼ o') , r) | F' =
    F'
⇝-f (↓ op V F) p  with ⇝-f-⇝ F p | ⇝-f F p
... | ((RR ‼ o') , r) | F' =
  ↓ op V F'
⇝-f (subsume p q F) r with ⇝-f-⇝ F r | ⇝-f F r
... | ((RR ‼ o') , s) | F' =
  F'


⇝-f-ty : {Γ : Ctx}
         {PP QQ : PType} →
         (F : Γ ⊢F⦂ PP) →
         (p : hole-ty-f F ⇝ QQ) →
         --------------------------
         QQ ≡ hole-ty-f (⇝-f F p)

⇝-f-ty [-] p =
  refl
⇝-f-ty (F ∥ₗ Q) p with ⇝-f-⇝ F p | ⇝-f F p | ⇝-f-ty F p
... | ((RR ‼ o') , q) | r | s =
  s
⇝-f-ty (P ∥ᵣ F) p with ⇝-f-⇝ F p | ⇝-f F p | ⇝-f-ty F p
... | ((RR ‼ o') , q) | r | s =
  s
⇝-f-ty (↑ op p V F) q with ⇝-f-⇝ F q | ⇝-f F q | ⇝-f-ty F q
... | ((RR ‼ o') , r) | s | t =
  t
⇝-f-ty (↓ op V F) p with ⇝-f-⇝ F p | ⇝-f F p | ⇝-f-ty F p
... | ((RR ‼ o') , q) | r | s =
  s
⇝-f-ty (subsume p q F) r with ⇝-f-⇝ F r | ⇝-f F r | ⇝-f-ty F r
... | ((RR ‼ o') , s) | t | u =
  u


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

infix 10 _[_]↝_

data _[_]↝_ {Γ : Ctx} : {PP : PType} → Γ ⊢P⦂ PP → {QQ : PType} → PP ⇝ QQ → Γ ⊢P⦂ QQ → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run   : {X : VType}
          {o : O}
          {i : I}
          {M N : Γ ⊢M⦂ X ! (o , i)} → 
          M ↝ N →
          ---------------------------
          (run M) [ id ]↝ (run N)

  -- BROADCAST RULES

  ↑-∥ₗ   : {PP QQ : PTypeShape}
           {o : O}
           {op : Σₙ} → 
           (p : op ∈ₒ o) →
           (V : Γ ⊢V⦂ `` (arₙ op)) →
           (P : Γ ⊢P⦂ PP ‼ o) →
           (Q : Γ ⊢P⦂ QQ ‼ o) →
           ------------------------------------------
           (↑ op p V P ∥ Q)
           [ par ⇝-refl ⇝-↓ ]↝
           (↑ op (∪ₒ-inl op p)
                 V
                 (subsume ⊑ₚ-refl ∪ₒ-inl P
                  ∥
                  subsume ⊑ₚ-refl ∪ₒ-inr (↓ op V Q)))

  ↑-∥ᵣ   : {PP QQ : PTypeShape}
           {o : O}
           {op : Σₙ} → 
           (p : op ∈ₒ o) →
           (V : Γ ⊢V⦂ `` (arₙ op)) →
           (P : Γ ⊢P⦂ PP ‼ o) →
           (Q : Γ ⊢P⦂ QQ ‼ o) →
           ----------------------------------------
           (P ∥ ↑ op p V Q)
           [ par ⇝-↓ ⇝-refl ]↝
           (↑ op (∪ₒ-inr op p)
                 V
                 (subsume ⊑ₚ-refl ∪ₒ-inl (↓ op V P)
                  ∥
                  subsume ⊑ₚ-refl ∪ₒ-inr Q))

  -- INTERRUPT RULES

  ↓-run : {X : VType}
          {o : O}
          {i : I}
          {op : Σₙ} → 
          (V : Γ ⊢V⦂ `` (arₙ op)) → 
          (M : Γ ⊢M⦂ X ! (o , i)) →
          -------------------------
          ↓ op V (run M)
          [ id ]↝
          run (↓ op V M)

  ↓-∥   : {PP QQ : PTypeShape}
          {o : O}
          {op : Σₙ}
          (V : Γ ⊢V⦂ `` (arₙ op)) →
          (P : Γ ⊢P⦂ PP ‼ o) →
          (Q : Γ ⊢P⦂ QQ ‼ o) →
          ----------------------------------------------------------------------
          ↓ op V (P ∥ Q)
          [ ⇝-refl ]↝
          (subsume ⊑ₚ-refl ∪ₒ-inl (↓ op V P) ∥ subsume ⊑ₚ-refl ∪ₒ-inr (↓ op V Q))

  ↓-↑   : {PP : PTypeShape}
          {o : O}
          {op : Σₙ}
          {op' : Σₙ} →
          (p : op' ∈ₒ o) →
          (V : Γ ⊢V⦂ ``(arₙ op)) →
          (W : Γ ⊢V⦂ ``(arₙ op')) →
          (P : Γ ⊢P⦂ PP ‼ o) →
          -----------------------------------
          ↓ op V (↑ op' p W P)
          [ ⇝-refl ]↝
          ↑ op' (↓ₚ-⊑ₒ PP op' p) W (↓ op V P)

  -- HOISTING RULE

  ↑     : {Δ : BCtx}
          {X : VType}
          {o o' : O}
          {i i' : I} → 
          (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) → 
          {op : Σₙ} → 
          (p : op ∈ₒ hole-ty-hₒ H) →
          (V : Γ ⋈ Δ ⊢V⦂ `` (arₙ op)) →
          (M : Γ ⋈ Δ ⊢M⦂ X ! (hole-ty-hₒ H , hole-ty-hᵢ H)) →
          ----------------------------------------------------------------------
          (run (H [ ↑ op p V M ]ₕ))
          [ id ]↝
          (↑ op (hole-ty-h-⊑ₒ H op p) (strengthen-val {Δ = Δ} V) (run (H [ M ]ₕ)))

  -- CONTEXT RULE

  context : {PP QQ : PType}
            {F : Γ ⊢F⦂ PP}
            {P : Γ ⊢P⦂ hole-ty-f F}
            {Q : Γ ⊢P⦂ QQ}
            {p : hole-ty-f F ⇝ QQ} → 
            P [ p ]↝ Q →
            ---------------
            F [ P ]f [ proj₂ (⇝-f-⇝ F p) ]↝ (⇝-f F p) [ subst (λ QQ → Γ ⊢P⦂ QQ) (⇝-f-ty F p) Q ]f

  -- SUBSUMPTION RULES

  subsume-run     : {X : VType}
                    {o o' : O}
                    {i i' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'} → 
                    (M : Γ ⊢M⦂ X ! (o , i)) →
                    -----------------------------
                    subsume (sub-run q) p (run M)
                    [ id ]↝
                    run (subsume p q M)

  subume-∥        : {PP PP' QQ QQ' : PTypeShape}
                    {o o' : O}
                    {p : PP ⊑ₚ PP'}
                    {q : QQ ⊑ₚ QQ'}
                    {r : o ⊑ₒ o'} → 
                    (P : Γ ⊢P⦂ PP ‼ o) →
                    (Q : Γ ⊢P⦂ QQ ‼ o) → 
                    --------------------------------
                    subsume (sub-par p q) r (P ∥ Q)
                    [ ⇝-refl ]↝
                    (subsume p r P) ∥ (subsume q r Q)

  subsume-↑       : {PP PP' : PTypeShape}
                    {o o' : O}
                    {op : Σₙ}
                    {p : PP ⊑ₚ PP'}
                    {q : o ⊑ₒ o'} → 
                    (r : op ∈ₒ o) →
                    (V : Γ ⊢V⦂ ``(arₙ op)) →
                    (P : Γ ⊢P⦂ PP ‼ o) →
                    -------------------------------
                    subsume p q (↑ op r V P)
                    [ ⇝-refl ]↝
                    ↑ op (q op r) V (subsume p q P)

  subsume-subsume : {PP PP' PP'' : PTypeShape}
                    {o o' o'' : O}
                    {p : PP ⊑ₚ PP'}
                    {p' : PP' ⊑ₚ PP''}
                    {q : o ⊑ₒ o'}
                    {q' : o' ⊑ₒ o''}
                    (P : Γ ⊢P⦂ PP ‼ o) →
                    -----------------------------------------
                    subsume p' q' (subsume p q P)
                    [ ⇝-refl ]↝
                    subsume (⊑ₚ-trans p p') (⊑ₒ-trans q q') P

-}
