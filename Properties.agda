open import Relation.Binary.HeterogeneousEquality hiding ([_])

open import Basic

dumb : {!!}
dumb = {!!}

module ForFree where
  wk⟦⟧ⁿᶠ-neˢᵉᵐ : ∀ {Γ Δ σ τ} (sub : Γ ⊂ Δ) (s : ⟦ Γ ⊢ⁿᵉ σ ⇒ τ ⟧)
               ->  wk⟦⟧ⁿᶠ sub (neˢᵉᵐ s) ≅ neˢᵉᵐ (wk⟦⟧ⁿᵉ sub s)
  wk⟦⟧ⁿᶠ-neˢᵉᵐ sub s = refl
