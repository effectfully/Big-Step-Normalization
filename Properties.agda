open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Basic
open import BigStep
open import SCV

wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ : ∀ {Γ Δ Θ σ} (κ : Δ ⊆ Θ) (ι : Γ ⊆ Δ) (v : σ ∈ Γ)
             -> wkᵛᵃʳ (κ ∘ᵒᵖᵉ ι) v ≡ wkᵛᵃʳ κ (wkᵛᵃʳ ι v)
wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ  stop     stop     ()
wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ (skip κ)  ι        v     = cong vs (wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ κ ι v)
wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ (keep κ) (skip ι)  v     = cong vs (wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ κ ι v)
wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ (keep κ) (keep ι)  vz    = refl
wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ (keep κ) (keep ι) (vs v) = cong vs (wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ κ ι v)        

mutual
  wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧)
              -> wk⟦⟧ⁿᶠ (κ ∘ᵒᵖᵉ ι) xˢ ≡ wk⟦⟧ⁿᶠ κ (wk⟦⟧ⁿᶠ ι xˢ)
  wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ (neˢᵉᵐ xˢ)  = cong neˢᵉᵐ (wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ xˢ)
  wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ (ƛˢᵉᵐ bˢ ρ) = cong (ƛˢᵉᵐ bˢ) (wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ ρ)

  wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧)
              -> wk⟦⟧ⁿᵉ (κ ∘ᵒᵖᵉ ι) xˢ ≡ wk⟦⟧ⁿᵉ κ (wk⟦⟧ⁿᵉ ι xˢ)
  wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ {κ = κ} {ι} (var v)   = cong var (wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ κ ι v)
  wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ             (fˢ ∙ xˢ) = cong₂ _∙_ (wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ fˢ) (wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ xˢ)

  wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ : ∀ {Γ Δ Θ Ξ} {κ : Θ ⊆ Ξ} {ι : Δ ⊆ Θ} (ρ : ⟦ Γ ↦ Δ ⟧)
               -> wk⟦⟧ᵉⁿᵛ (κ ∘ᵒᵖᵉ ι) ρ ≡ wk⟦⟧ᵉⁿᵛ κ (wk⟦⟧ᵉⁿᵛ ι ρ)
  wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ  εᵉⁿᵛ       = refl
  wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ (ρ ▻ᵉⁿᵛ xˢ) = cong₂ _▻ᵉⁿᵛ_ (wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ ρ) (wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ xˢ)

mutual
  wk-Quoteⁿᶠ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧} {xʳ : Γ ⊢ⁿᶠ σ}
             -> Quoteⁿᶠ xˢ ⇓ xʳ -> Quoteⁿᶠ wk⟦⟧ⁿᶠ ι xˢ ⇓ wkⁿᶠ ι xʳ
  wk-Quoteⁿᶠ (ne⇓ qx)    = ne⇓ (wk-Quoteⁿᵉ qx)
  wk-Quoteⁿᶠ (ƛ⇓_ qy qb) = (ƛ⇓ {!!}) (wk-Quoteⁿᶠ qb)

  wk-Quoteⁿᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} {xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧} {xʳ : Γ ⊢ⁿᵉ σ}
             -> Quoteⁿᵉ xˢ ⇓ xʳ -> Quoteⁿᵉ wk⟦⟧ⁿᵉ ι xˢ ⇓ wkⁿᵉ ι xʳ
  wk-Quoteⁿᵉ  var⇓      = var⇓
  wk-Quoteⁿᵉ (qf ∙⇓ qx) = wk-Quoteⁿᵉ qf ∙⇓ wk-Quoteⁿᶠ qx

wkˢᶜᵛ : ∀ {Γ Δ σ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧}
      -> (ι : Γ ⊆ Δ) -> SCV xˢ -> SCV (wk⟦⟧ⁿᶠ ι xˢ)
wkˢᶜᵛ {σ = ⋆}     {neˢᵉᵐ xˢ} ι (x , qx) = wkⁿᵉ ι x , wk-Quoteⁿᵉ qx
wkˢᶜᵛ {σ = σ ⇒ τ}            ι  r       = λ κ xˢᶜᵛ ->
  case r (κ ∘ᵒᵖᵉ ι) xˢᶜᵛ of λ{
    (yˢ , yʳ , yˢᶜᵛ) -> yˢ , subst (_$ _ ⇓ yˢ) (wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ _) yʳ , yˢᶜᵛ
  }
