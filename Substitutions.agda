open import AEff
open import Renamings
open import Types hiding (``)

open import Relation.Binary.PropositionalEquality hiding ([_])

module Substitutions where

-- SET OF SUBSTITUTIONS BETWEEN CONTEXTS

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : Type} → X ∈ Γ → Γ' ⊢V⦂ X


-- IDENTITY AND EXTENSION SUBSTITUTIONS

id-subst : {Γ : Ctx} → Sub Γ Γ
id-subst x = ` x

_[_]s : {Γ Γ' : Ctx} {X : Type} → Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl x) = s x


-- LIFTING SUBSTITUTIONS

lift : {Γ Γ' : Ctx} {X : Type} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)


-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  infix 40 _[_]v
  infix 40 _[_]m

  _[_]v : {Γ Γ' : Ctx} → {X : Type} → Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X
  (` x) [ s ]v =
    s x
  (`` c) [ s ]v =
    `` c
  (ƛ M) [ s ]v =
    ƛ (M [ lift s ]m)
  ⟨ V ⟩ [ s ]v =
    ⟨ V [ s ]v ⟩
  ★ [ s ]v =
    ★

  _[_]m : {Γ Γ' : Ctx} → {C : Type} → Γ ⊢M⦂ C → Sub Γ Γ'  → Γ' ⊢M⦂ C
  (return V) [ s ]m =
    return (V [ s ]v)
  (let= M `in N) [ s ]m =
    let= (M [ s ]m) `in (N [ lift s ]m)
  (V · W) [ s ]m =
    (V [ s ]v) · (W [ s ]v)
  (↑ op V M) [ s ]m =
    ↑ op (V [ s ]v) (M [ s ]m)
  (↓ op V M) [ s ]m =
    ↓ op (V [ s ]v) (M [ s ]m)
  (promise op ↦ M `in N) [ s ]m =
    promise op ↦ (M [ lift s ]m) `in (N [ lift s ]m)
  (await V until M) [ s ]m =
    await (V [ s ]v) until (M [ lift s ]m)


-- ACTION OF SUBSTITUTION ON WELL-TYPED TERMS

infix 40 _[_]p

_[_]p : {Γ Γ' : Ctx} {PP : PType} → Γ ⊢P⦂ PP → Sub Γ Γ' → Γ' ⊢P⦂ PP
(run M) [ s ]p =
  run (M [ s ]m)
(P ∥ Q) [ s ]p =
  (P [ s ]p) ∥ (Q [ s ]p)
(↑ op V P) [ s ]p =
  ↑ op (V [ s ]v) (P [ s ]p)
(↓ op V P) [ s ]p =
  ↓ op (V [ s ]v) (P [ s ]p)
