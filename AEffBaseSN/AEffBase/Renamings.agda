open import AEffBaseSN.AEffBase.Types
open import AEffBaseSN.AEffBase.AEff

module AEffBaseSN.AEffBase.Renamings where

-- SET OF RENAMINGS BETWEEN CONTEXTS

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : Type} → X ∈ Γ → X ∈ Γ'

variable
  r r' r'' : Ren Γ Γ'


-- IDENTITY, COMPOSITION, AND EXCHANGE RENAMINGS

id-ren : Ren Γ Γ 
id-ren x = x


-- WEAKENING OF RENAMINGS

wk₁ : Ren Γ (Γ ∷ X)
wk₁ = Tl

wk₂ : Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
wk₂ f Hd = Hd
wk₂ f (Tl v) = Tl (f v)


-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

V-rename : Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X

M-rename : Ren Γ Γ' → Γ ⊢M⦂ X → Γ' ⊢M⦂ X

V-rename f (` x) =
  ` f x
V-rename f (`` c) =
  `` c
V-rename f (ƛ M) =
  ƛ (M-rename (wk₂ f) M)
V-rename f ⟨ V ⟩ =
  ⟨ V-rename f V ⟩

M-rename f (return V) =
  return (V-rename f V)
M-rename f (let= M `in N) =
  let= M-rename f M `in M-rename (wk₂ f) N
M-rename f (V · W) =
  (V-rename f V) · (V-rename f W)
M-rename f (↑ op V M) =
  ↑ op (V-rename f V) (M-rename f M)
M-rename f (↓ op V M) =
  ↓ op (V-rename f V) (M-rename f M)
M-rename f (promise op ↦ M `in N) =
  promise op ↦ M-rename (wk₂ f) M `in M-rename (wk₂ f) N
M-rename f (await V until M) =
  await V-rename f V until M-rename (wk₂ f) M