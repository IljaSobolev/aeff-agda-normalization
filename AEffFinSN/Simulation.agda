open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import AEffFinSN.AEffFin
import AEffStarSN.AEffStar as B

module AEffFinSN.Simulation where

emb-ty-v : VType → B.Type

emb-ty-c : CType → B.Type

emb-ty-v (``` x) = B.``` x
emb-ty-v (X ⇒ C) = emb-ty-v X B.⇒ emb-ty-c C
emb-ty-v ⟨ X ⟩ = B.⟨ emb-ty-v X ⟩

emb-ty-c (X ! _) = emb-ty-v X

emb-ctx : Ctx → B.Ctx
emb-ctx [] = B.[]
emb-ctx (Γ ∷ X) = emb-ctx Γ B.∷ emb-ty-v X

emb-∈ : X ∈ Γ → emb-ty-v X B.∈ emb-ctx Γ
emb-∈ Hd = B.Hd
emb-∈ (Tl x) = B.Tl (emb-∈ x)

emb-tm-v : Γ ⊢V⦂ X → emb-ctx Γ B.⊢V⦂ emb-ty-v X

emb-tm-m : Γ ⊢M⦂ C → emb-ctx Γ B.⊢M⦂ emb-ty-c C

emb-tm-v (` x) = B.` emb-∈ x
emb-tm-v (`` c) = B.`` c
emb-tm-v (ƛ M) = B.ƛ (emb-tm-m M)
emb-tm-v ⟨ V ⟩ = B.⟨ emb-tm-v V ⟩

emb-tm-m (return V) = B.return (emb-tm-v V)
emb-tm-m (V · W) = emb-tm-v V B.· emb-tm-v W
emb-tm-m (let= M `in N) = B.let= (emb-tm-m M) `in (emb-tm-m N)
emb-tm-m (↑ op V M) = B.↑ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (↓ {C = _ ! _} op V M) = B.↓ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (promise op ∣ p ↦ M `in N) = B.promise op ↦ emb-tm-m M `in emb-tm-m N
emb-tm-m (await V until N) = B.await emb-tm-v V until emb-tm-m N
emb-tm-m (coerce p M) = B.coerce (emb-tm-m M)

infix 4 _~ᵣ_
_~ᵣ_ : (r : Ren Γ Δ) (r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)) → Set
r ~ᵣ r† = {X : VType} (x : X ∈ _) → emb-∈ (r x) ≡ r† (emb-∈ x)

~ᵣ-v : (V : Γ ⊢V⦂ X) →
       {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
       r ~ᵣ r† →
       ------------
       emb-tm-v (V-rename r V) ≡ B.V-rename r† (emb-tm-v V)

~ᵣ-m : (M : Γ ⊢M⦂ C)
       {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
       r ~ᵣ r† →
       ------------
       emb-tm-m (M-rename r M) ≡ B.M-rename r† (emb-tm-m M)

~ᵣ-lift : (M : Γ ∷ X ⊢M⦂ C)
          {r : Ren Γ Δ} {r† : B.Ren (emb-ctx Γ) (emb-ctx Δ)} →
          r ~ᵣ r† →
          ------------
          emb-tm-m (M-rename (wk₂ r) M) ≡ B.M-rename (B.wk₂ r†) (emb-tm-m M)
~ᵣ-lift M ~r = ~ᵣ-m M (λ {Hd → refl; (Tl x) → cong B.Tl (~r x)})

~ᵣ-v (` x) ~r = cong B.`_ (~r x)
~ᵣ-v (`` c) ~r = refl
~ᵣ-v (ƛ M) ~r = cong B.ƛ (~ᵣ-lift M ~r)
~ᵣ-v ⟨ V ⟩ ~r = cong B.⟨_⟩ (~ᵣ-v V ~r)

~ᵣ-m (return V) ~r = cong B.return (~ᵣ-v V ~r)
~ᵣ-m (let= M `in N) ~r = cong₂ B.let=_`in_ (~ᵣ-m M ~r) (~ᵣ-lift N ~r)
~ᵣ-m (V · W) ~r = cong₂ B._·_ (~ᵣ-v V ~r) (~ᵣ-v W ~r)
~ᵣ-m (↑ op V M) ~r = cong₂ (B.↑ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (↓ {C = _ ! _} op V M) ~r = cong₂ (B.↓ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (promise op ∣ p ↦ M `in N) ~r = cong₂ (B.promise op ↦_`in_) (~ᵣ-lift M ~r) (~ᵣ-lift N ~r)
~ᵣ-m (await V until N) ~r = cong₂ (B.await_until_) (~ᵣ-v V ~r) (~ᵣ-lift N ~r)
~ᵣ-m (coerce p M) ~r = cong B.coerce (~ᵣ-m M ~r)

infix 4 _~ₛ_
_~ₛ_ : (s : Sub Γ Δ) (s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)) → Set
s ~ₛ s† = {X : VType} (x : X ∈ _) → emb-tm-v (s x) ≡ s† (emb-∈ x)

~ₛ-v : (V : Γ ⊢V⦂ X)
       {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
       s ~ₛ s† →
       ------------
       emb-tm-v (V [ s ]v) ≡ emb-tm-v V B.[ s† ]v

~ₛ-m : (M : Γ ⊢M⦂ C)
       {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
       s ~ₛ s† →
       ------------
       emb-tm-m (M [ s ]m) ≡ emb-tm-m M B.[ s† ]m

~ₛ-lift : (M : Γ ∷ X ⊢M⦂ C)
          {s : Sub Γ Δ} {s† : B.Sub (emb-ctx Γ) (emb-ctx Δ)} →
          s ~ₛ s† →
          ------------
          emb-tm-m (M [ lift s ]m) ≡ (emb-tm-m M) B.[ B.lift s† ]m
~ₛ-lift M ~s = ~ₛ-m M (λ {Hd → refl; (Tl x) → trans (~ᵣ-v _ (λ _ → refl)) (cong (B.V-rename B.Tl) (~s x))})

~ₛ-v (` x) ~s = ~s x
~ₛ-v (`` c) ~s = refl
~ₛ-v (ƛ M) ~s = cong B.ƛ (~ₛ-lift M ~s)
~ₛ-v ⟨ V ⟩ ~s = cong B.⟨_⟩ (~ₛ-v V ~s)

~ₛ-m (return V) ~s = cong B.return (~ₛ-v V ~s)
~ₛ-m (let= M `in N) ~s = cong₂ B.let=_`in_ (~ₛ-m M ~s) (~ₛ-lift N ~s)
~ₛ-m (V · W) ~s = cong₂ B._·_ (~ₛ-v V ~s) (~ₛ-v W ~s)
~ₛ-m (↑ op V M) ~s = cong₂ (B.↑ op) (~ₛ-v V ~s) (~ₛ-m M ~s)
~ₛ-m (↓ {C = _ ! _} op V M) ~s = cong₂ (B.↓ op) (~ₛ-v V ~s) (~ₛ-m M ~s)
~ₛ-m (promise op ∣ p ↦ M `in N) ~s = cong₂ (B.promise op ↦_`in_) (~ₛ-lift M ~s) (~ₛ-lift N ~s)
~ₛ-m (await V until N) ~s = cong₂ (B.await_until_) (~ₛ-v V ~s) (~ₛ-lift N ~s)
~ₛ-m (coerce p M) ~s = cong B.coerce (~ₛ-m M ~s)

~ᵣ-wk₁-v : (V : Γ ⊢V⦂ X) →
           -----------
           emb-tm-v (V-rename (wk₁ {X = Z}) V) ≡ B.V-rename B.wk₁ (emb-tm-v V)
~ᵣ-wk₁-v V = ~ᵣ-v V (λ _ → refl)

~ᵣ-wk₂-wk₁-m : (M : Γ ∷ X ⊢M⦂ C) →
               -----------
               emb-tm-m (M-rename (wk₂ (wk₁ {X = Z})) M) ≡ B.M-rename (B.wk₂ B.wk₁) (emb-tm-m M)
~ᵣ-wk₂-wk₁-m M = ~ᵣ-m M (λ {Hd → refl; (Tl x) → refl})

~ₛᵣ-m : (M : Γ ∷ X ⊢M⦂ C) (V : Γ ⊢V⦂ X) →
        -----------
        emb-tm-m (M [ id-subst [ V ]s ]m) ≡ emb-tm-m M B.[ B.ids B.[ emb-tm-v V ]s ]m
~ₛᵣ-m M V = ~ₛ-m M (λ {Hd → refl; (Tl x) → refl})

~-strengthen : (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A) →
               -----------------------
               emb-tm-v (strengthen-val V) ≡ B.strengthen-val (emb-tm-v V)
~-strengthen (` Tl x) = refl
~-strengthen (`` c) = refl

sim : M ↝ N → emb-tm-m M B.↝ emb-tm-m N
sim (apply M V) rewrite ~ₛᵣ-m M V = B.apply _ _
sim (let-return V N) rewrite ~ₛᵣ-m N V = B.let-return _ _
sim (let-↑ V M N) = B.T-↑ _ _ _
sim (let-promise {X = X} p M₁ M₂ N) rewrite ~ᵣ-wk₂-wk₁-m {Z = ⟨ X ⟩} N = B.T-promise _ _ _
sim (promise-↑ p V M N) rewrite ~-strengthen V = B.promise-↑ _ _ _
sim (↓-return V W) = B.↓-return _ _
sim (↓-↑ V W M) = B.T-↑ _ _ _
sim (↓-promise-op {X = X} p V M N) rewrite ~ₛᵣ-m M V | ~ᵣ-wk₁-v {Z = ⟨ X ⟩} V = B.↓-promise-op _ _ _
sim (↓-promise-op' {X = X} V p q M N) rewrite ~ᵣ-wk₁-v {Z = ⟨ X ⟩} V = B.T-promise _ _ _
sim (await-promise V N) rewrite ~ₛᵣ-m N V = B.await-promise _ _
sim (context-let r) = B.context-T _ (sim r)
sim (context-↑ r) = B.context-↑ (sim r)
sim (context-↓ {_} {_ ! _} r) = B.context-T _ (sim r)
sim (context-promise r) = B.context-promise (sim r)
sim (coerce-return V) = B.coerce-return _
sim (coerce-↑ V M) = B.T-↑ _ _ _
sim (coerce-promise p M N) = B.T-promise _ _ _