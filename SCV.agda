open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Basic
open import BigStep
open import Convertibility

SCV : ∀ {σ Γ} -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> Set
SCV {⋆}     (neˢᵉᵐ xˢ) = ∃ λ xʳ -> Quoteⁿᵉ xˢ ⇓ xʳ × emb⟦⟧ⁿᵉ xˢ ≈ embⁿᵉ xʳ
SCV {σ ⇒ τ}  fˢ        = ∀ {Δ} (ι : _ ⊆ Δ) {xˢ} -> SCV xˢ ->
  ∃ λ yˢʳ -> wk⟦⟧ⁿᶠ ι fˢ $ xˢ ⇓ yˢʳ
           × SCV yˢʳ
           × emb⟦⟧ⁿᶠ (wk⟦⟧ⁿᶠ ι fˢ) ∙ emb⟦⟧ⁿᶠ xˢ ≈ emb⟦⟧ⁿᶠ yˢʳ

data SCE {Δ} : ∀ {Γ} -> ⟦ Γ ↦ Δ ⟧ -> Set where
  εˢᶜᵉ   : SCE εᵉⁿᵛ
  _▻ˢᶜᵉ_ : ∀ {Γ σ} {ρ : ⟦ Γ ↦ Δ ⟧} {xˢ : ⟦ Δ ⊢ⁿᶠ σ ⟧}
         -> SCE ρ -> SCV xˢ -> SCE (ρ ▻ᵉⁿᵛ xˢ)
    
