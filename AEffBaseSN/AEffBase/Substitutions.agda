open import AEffBaseSN.AEffBase.Types
open import AEffBaseSN.AEffBase.AEff
open import AEffBaseSN.AEffBase.Renamings

module AEffBaseSN.AEffBase.Substitutions where

-- SET OF SUBSTITUTIONS BETWEEN CONTEXTS

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : Type} → X ∈ Γ → Γ' ⊢V⦂ X

variable
  s s' s'' : Sub Γ Γ'


-- IDENTITY AND EXTENSION SUBSTITUTIONS

id-subst : Sub Γ Γ
id-subst x = ` x

_[_]s : Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl x) = s x


-- LIFTING SUBSTITUTIONS

lift : Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)


-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

infix 40 _[_]v
infix 40 _[_]m

_[_]v : Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X

_[_]m : Γ ⊢M⦂ X → Sub Γ Γ' → Γ' ⊢M⦂ X

(` x) [ s ]v =
  s x
(`` c) [ s ]v =
  `` c
(ƛ M) [ s ]v =
  ƛ (M [ lift s ]m)
⟨ V ⟩ [ s ]v =
  ⟨ V [ s ]v ⟩

(return V) [ s ]m =
  return (V [ s ]v)
(let= M `in N) [ s ]m =
  let= M [ s ]m `in N [ lift s ]m
(V · W) [ s ]m =
  (V [ s ]v) · (W [ s ]v)
(↑ op V M) [ s ]m =
  ↑ op (V [ s ]v) (M [ s ]m)
(↓ op V M) [ s ]m =
  ↓ op (V [ s ]v) (M [ s ]m)
(promise op ↦ M `in N) [ s ]m =
  promise op ↦ M [ lift s ]m `in N [ lift s ]m
(await V until M) [ s ]m =
  await V [ s ]v until M [ lift s ]m