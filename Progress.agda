open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import AwaitingComputations
open import Preservation
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module Progress where

-- WRAPPING PROMISES AROUND A CONTEXT

⟨⟨_⟩⟩ : Ctx → Ctx
⟨⟨ [] ⟩⟩ = []
⟨⟨ Γ ∷ X ⟩⟩ = ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩


-- RESULTS

data RunResult⟨_∣_⟩ (Γ : Ctx) : {C : Type} → ⟨⟨ Γ ⟩⟩ ⊢M⦂ C → Set where

  return   : {X : Type}
             (V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X) →
             ------------------------------------------
             RunResult⟨ Γ ∣ return V ⟩

  promise  : {X Y : Type}
             {op : Σₛ}
             {M : ⟨⟨ Γ ⟩⟩ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩}
             {N : ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩ ⊢M⦂ Y} →
             RunResult⟨ Γ ∷ X ∣ N ⟩ →
             ----------------------------------------------------
             RunResult⟨ Γ ∣ promise op ↦ M `in N ⟩

  awaiting : {C : Type}
             {Y : Type}
             {y : ⟨ Y ⟩ ∈ ⟨⟨ Γ ⟩⟩}
             {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
             y ⧗ M →
             ---------------------
             RunResult⟨ Γ ∣ M ⟩

data CompResult⟨_∣_⟩ (Γ : Ctx) : {C : Type} → ⟨⟨ Γ ⟩⟩ ⊢M⦂ C → Set where

  comp   : {C : Type}
           {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} →
           RunResult⟨ Γ ∣ M ⟩ →
           ---------------------
           CompResult⟨ Γ ∣ M ⟩

  signal : {X : Type}
           {op : Σₛ}
           {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ ``(payload op)}
           {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X} →
           CompResult⟨ Γ ∣ M ⟩ →
           --------------------------------
           CompResult⟨ Γ ∣ ↑ op V M ⟩


-- PROGRESS THEOREM FOR PROMISE-OPEN COMPUTATIONS

⇒-not-in-ctx : {Γ : Ctx} {X : Type} {C : Type} → X ⇒ C ∈ ⟨⟨ Γ ⟩⟩ → ⊥
⇒-not-in-ctx {Γ ∷ y} (Tl x) =
  ⇒-not-in-ctx x


{- THEOREM 3.3 -}  

progress : {Γ : Ctx}
           {C : Type} →
           (M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C) →
           -------------------------------
           (Σ[ N ∈ ⟨⟨ Γ ⟩⟩ ⊢M⦂ C ] (M ↝ N)
            ⊎
            CompResult⟨ Γ ∣ M ⟩)

progress (return V) =
  inj₂ (comp (return V))
progress (let= M `in N) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , context (let= [-] `in N) r)
... | inj₂ (comp (return V)) =
  inj₁ (_ , let-return V N)
... | inj₂ (comp (promise {_} {_} {_} {M'} {M''} R)) =
  inj₁ (_ , let-promise M' M'' N)
... | inj₂ (comp (awaiting R)) =
  inj₂ (comp (awaiting (let-in R)))
... | inj₂ (signal {_} {_} {V} {M'} R) =
  inj₁ (_ , let-↑ V M' N)
progress ((` x) · W) with ⇒-not-in-ctx x
... | ()
progress (ƛ M · W) =
  inj₁ (_ , apply M W)
progress (↑ op V M) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , context (↑ op V [-]) r)
... | inj₂ R =
  inj₂ (signal R)
progress (↓ op V M) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , context (↓ op V [-]) r)
... | inj₂ (comp (return W)) =
  inj₁ (_ , (↓-return V W))
... | inj₂ (comp (awaiting R)) =
  inj₂ (comp (awaiting (interrupt R)))
... | inj₂ (signal {X} {op'} {W} {M'} R) =
  inj₁ (_ , (↓-↑ V W M'))
... | inj₂ (comp (promise {_} {_} {op'} {M'} {M''} R)) with decₛ op op'
... | yes refl =
  inj₁ (_ , ↓-promise-op V M' M'')
... | no ¬q =
  inj₁ (_ , ↓-promise-op' ¬q V M' M'')
progress (promise op ↦ M `in N) with progress N
... | inj₁ (M' , r) =
  inj₁ (_ , context (promise op ↦ M `in [-]) r)
... | inj₂ (comp R) =
  inj₂ (comp (promise R))
... | inj₂ (signal {_} {_} {V} {M'} R) =
  inj₁ (_ , promise-↑ V M M')
progress (await ` x until M) =
  inj₂ (comp (awaiting await))
progress (await ⟨ V ⟩ until M) =
  inj₁ (_ , await-promise V M)


-- PROGRESS THEOREM FOR CLOSED COMPUTATIONS

{- COROLLARY 3.4 -}

closed-progress : {C : Type} →
                  (M : [] ⊢M⦂ C) →
                  --------------------------
                  (Σ[ N ∈ [] ⊢M⦂ C ] (M ↝ N)
                   ⊎
                   CompResult⟨ [] ∣ M ⟩)

closed-progress M =
  progress M
