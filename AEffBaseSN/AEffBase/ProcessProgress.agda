open import AEffBaseSN.AEffBase.Types
open import AEffBaseSN.AEffBase.AEff
open import AEffBaseSN.AEffBase.Progress
open import AEffBaseSN.AEffBase.ProcessPreservation

open import AEff.EffectAnnotations using (Σₛ)
open import AEff.AEff using (payload)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_)

module AEffBaseSN.AEffBase.ProcessProgress where

-- PROCESS RESULTS

data ParResult⟨_⟩ : [] ⊢P⦂ PP → Set where

  run : RunResult⟨ [] ∣ M ⟩ →
        ------------------
        ParResult⟨ run M ⟩

  par : ParResult⟨ P ⟩ →
        ParResult⟨ Q ⟩ →
        ------------------
        ParResult⟨ P ∥ Q ⟩

data ProcResult⟨_⟩ : [] ⊢P⦂ PP → Set where

  proc   : ParResult⟨ P ⟩ →
           ----------------
           ProcResult⟨ P ⟩

  signal : ProcResult⟨ P ⟩ →
           -----------------------
           ProcResult⟨ ↑ op V P ⟩


-- PROGRESS THEOREM FOR PROCESSES

{- THEOREM 4.3 -}

proc-progress : (P : [] ⊢P⦂ PP) →
                -------------------------
                Σ[ Q ∈ [] ⊢P⦂ PP ] P ↝ₚ Q
                ⊎
                ProcResult⟨ P ⟩
proc-progress (run M) with progress M
... | inj₁ (_ , r) = inj₁ (_ , run r)
... | inj₂ (comp R) = inj₂ (proc (run R))
... | inj₂ (signal R) = inj₁ (_ , ↑ _ _)
proc-progress (P ∥ Q) with proc-progress P
... | inj₁ (_ , r) = inj₁ (_ , context ([-] ∥ₗ Q) r)
... | inj₂ (signal _) = inj₁ (_ , ↑-∥ₗ _ _ Q)
... | inj₂ (proc R) with proc-progress Q
...   | inj₁ (_ , r) = inj₁ (_ , context (P ∥ᵣ [-]) r)
...   | inj₂ (proc R') = inj₂ (proc (par R R'))
...   | inj₂ (signal _) = inj₁ (_ , ↑-∥ᵣ _ P _)
proc-progress (↑ op V P) with proc-progress P
... | inj₁ (_ , r) = inj₁ (_ , context (↑ _ _ _) r)
... | inj₂ R = inj₂ (signal R)
proc-progress (↓ op V P) with proc-progress P
... | inj₁ (_ , r) = inj₁ (_ , context (↓ _ _ _) r)
... | inj₂ (proc (run _)) = inj₁ (_ , ↓-run _ _)
... | inj₂ (proc (par _ _)) = inj₁ (_ , ↓-∥ _ _ _)
... | inj₂ (signal _) = inj₁ (_ , ↓-↑ _ _ _)