open import AEffBaseSN.AEffBase.Types
open import AEffBaseSN.AEffBase.AEff
open import AEffBaseSN.AEffBase.Preservation

open import AEff.EffectAnnotations using (Σₛ; decₛ)

open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (yes; no)

module AEffBaseSN.AEffBase.Progress where

-- WRAPPING PROMISES AROUND A CONTEXT

⟨⟨_⟩⟩ : Ctx → Ctx
⟨⟨ [] ⟩⟩ = []
⟨⟨ Γ ∷ X ⟩⟩ = ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩


-- RESULTS

data RunResult⟨_∣_⟩ (Γ : Ctx) : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X → Set where

  return  : (V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X) →
            -------------------------
            RunResult⟨ Γ ∣ return V ⟩

  promise : RunResult⟨ Γ ∷ X ∣ N ⟩ →
            -------------------------------------
            RunResult⟨ Γ ∣ promise op ↦ M `in N ⟩

  await   : (p : ⟨ X ⟩ ∈ ⟨⟨ Γ ⟩⟩) →
            ----------------------------------
            RunResult⟨ Γ ∣ await ` p until M ⟩


data CompResult⟨_∣_⟩ (Γ : Ctx) : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X → Set where

  comp   : RunResult⟨ Γ ∣ M ⟩ →
           -------------------
           CompResult⟨ Γ ∣ M ⟩

  signal : CompResult⟨ Γ ∣ M ⟩ →
           --------------------------
           CompResult⟨ Γ ∣ ↑ op V M ⟩


-- PROGRESS THEOREM FOR PROMISE-OPEN COMPUTATIONS

⇒-not-in-ctx : X ⇒ Y ∈ ⟨⟨ Γ ⟩⟩ → ⊥
⇒-not-in-ctx {Γ = _ ∷ _} (Tl x) = ⇒-not-in-ctx x

progress : (M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X) →
           -------------------------------
           Σ[ N ∈ ⟨⟨ Γ ⟩⟩ ⊢M⦂ X ] M ↝ N
           ⊎
           CompResult⟨ Γ ∣ M ⟩

progress (return V) =
  inj₂ (comp (return V))
progress (let= M `in N) with progress M
... | inj₁ (_ , r) =
  inj₁ (_ , context _ r)
... | inj₂ (comp (return _)) =
  inj₁ (_ , let-return _ _)
... | inj₂ (comp (promise R)) =
  inj₁ (_ , let-promise _ _ _)
... | inj₂ (comp (await p)) =
  inj₁ (_ , let-await _ (` p) _)
... | inj₂ (signal R) =
  inj₁ (_ , let-↑ _ _ _)
progress ((` x) · W) = ⊥-elim (⇒-not-in-ctx x)
progress (ƛ M · W) =
  inj₁ (_ , apply M W)
progress (↑ op V M) with progress M
... | inj₁ (_ , r) =
  inj₁ (_ , context _ r)
... | inj₂ R =
  inj₂ (signal R)
progress (↓ op V M) with progress M
... | inj₁ (_ , r) =
  inj₁ (_ , context _ r)
... | inj₂ (comp (return W)) =
  inj₁ (_ , (↓-return V W))
... | inj₂ (comp (await p)) =
  inj₁ (_ , ↓-await _ (` p) _)
... | inj₂ (signal R) =
  inj₁ (_ , ↓-↑ _ _ _)
... | inj₂ (comp (promise {op = op'} R)) with decₛ op' op
... | yes refl =
  inj₁ (_ , ↓-promise-op _ _ _)
... | no ¬q =
  inj₁ (_ , ↓-promise-op' ¬q _ _ _)
progress (promise op ↦ M `in N) with progress N
... | inj₁ (_ , r) =
  inj₁ (_ , context _ r)
... | inj₂ (comp R) =
  inj₂ (comp (promise R))
... | inj₂ (signal R) =
  inj₁ (_ , promise-↑ _ _ _)
progress (await ` x until M) =
  inj₂ (comp (await x))
progress (await ⟨ V ⟩ until M) =
  inj₁ (_ , await-promise V M)


-- PROGRESS THEOREM FOR CLOSED COMPUTATIONS

closed-progress : (M : [] ⊢M⦂ X) →
                  --------------------------
                  Σ[ N ∈ [] ⊢M⦂ X ] M ↝ N
                   ⊎
                   CompResult⟨ [] ∣ M ⟩
                   
closed-progress M = progress M