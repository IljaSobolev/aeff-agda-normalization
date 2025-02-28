open import Data.Empty
open import Data.List renaming (_∷_ to _∷ₗ_ ; [_] to [_]ₗ)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import Preservation
open import ProcessPreservation
open import Progress
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module ProcessProgress where

-- PROCESS RESULTS

data ParResult⟨_⟩ : {PP : PType} → [] ⊢P⦂ PP → Set where

  run    : {X : Type}
           {M : [] ⊢M⦂ X} →
           RunResult⟨ [] ∣ M ⟩ →
           --------------------------
           ParResult⟨ run M ⟩

  par    : {PP : PType}
           {QQ : PType}
           {P : [] ⊢P⦂ PP}
           {Q : [] ⊢P⦂ QQ} →
           ParResult⟨ P ⟩ →
           ParResult⟨ Q ⟩ →
           ------------------
           ParResult⟨ P ∥ Q ⟩

data ProcResult⟨_⟩ : {PP : PType} → [] ⊢P⦂ PP → Set where

  proc   : {PP : PType}
           {P : [] ⊢P⦂ PP} →
           ParResult⟨ P ⟩ →
           -----------------
           ProcResult⟨ P ⟩

  signal : {PP : PType}
           {op : Σₛ}
           {V : [] ⊢V⦂ ``(payload op)}
           {P : [] ⊢P⦂ PP} →
           ProcResult⟨ P ⟩ →
           ---------------------------
           ProcResult⟨ ↑ op V P ⟩


-- PROGRESS THEOREM FOR PROCESSES

{- THEOREM 4.3 -}

proc-progress : {PP : PType} →
                (P : [] ⊢P⦂ PP) →
                -------------------------------------------------------------------------------
                (Σ[ Q ∈ [] ⊢P⦂ PP ] (P ↝P Q)
                 ⊎
                 ProcResult⟨ P ⟩)

proc-progress (run {X} M) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , run r)
... | inj₂ (comp R) =
  inj₂ (proc (run R))
... | inj₂ (signal {_} {_} {V} {Q} R) =
  inj₁ (_ , ↑ V Q)
proc-progress (P ∥ Q) with proc-progress P
... | inj₁ (P' , r') =
  inj₁ (_ , context ([-] ∥ₗ Q) r')
... | inj₂ R with proc-progress Q
... | inj₁ (Q' , r') =
  inj₁ (_ , context (P ∥ᵣ [-]) r')
proc-progress (P ∥ Q) | inj₂ (proc R) | inj₂ (proc R') =
  inj₂ (proc (par R R'))
proc-progress (P ∥ .(↑ _ _ _)) | inj₂ R | inj₂ (signal {_} {_} {V} {Q} R') =
  inj₁ (_ , ↑-∥ᵣ V P Q)
proc-progress (.(↑ _ _ _) ∥ Q) | inj₂ (signal {_} {_} {V} {P} R) | inj₂ R' =
  inj₁ (_ , ↑-∥ₗ V P Q)
proc-progress (↑ op V P) with proc-progress P
... | inj₁ (P' , r') =
  inj₁ (_ , context (↑ op V [-]) r')
... | inj₂ R =
  inj₂ (signal R)
proc-progress (↓ op V P) with proc-progress P
... | inj₁ (P' , r') =
  inj₁ (_ , context (↓ op V [-]) r')
... | inj₂ (proc (run {_} {M} R)) =
  inj₁ (_ , ↓-run V M)
... | inj₂ (proc (par {_} {_} {Q} {Q'} R R')) =
  inj₁ (_ , ↓-∥ V Q Q')
... | inj₂ (signal {_} {_} {W} {Q} R) =
  inj₁ (_ , ↓-↑ V W Q)
