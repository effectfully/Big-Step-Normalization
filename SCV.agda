open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Basic
open import BigStep

SCV : ∀ {σ Γ} -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> Set
SCV {⋆}     (neˢᵉᵐ n) = ∃ (Quoteⁿᵉ n ⇓_)
SCV {σ ⇒ τ}  fˢ       = ∀ {Δ} (ι : _ ⊆ Δ) {xˢ} -> SCV xˢ ->
  ∃ λ yˢʳ -> wk⟦⟧ⁿᶠ ι fˢ $ xˢ ⇓ yˢʳ × SCV yˢʳ

data SCE {Δ} : ∀ {Γ} -> ⟦ Γ ↦ Δ ⟧ -> Set where
  εˢᶜᵉ   : SCE εᵉⁿᵛ
  _▻ˢᶜᵉ_ : ∀ {Γ σ} {ρ : ⟦ Γ ↦ Δ ⟧} {xˢ : ⟦ Δ ⊢ⁿᶠ σ ⟧}
         -> SCE ρ -> SCV xˢ -> SCE (ρ ▻ᵉⁿᵛ xˢ)
    
