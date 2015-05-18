open import Function hiding (_$_)
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
  wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧}
              -> wk⟦⟧ⁿᶠ (κ ∘ᵒᵖᵉ ι) xˢ ≡ wk⟦⟧ⁿᶠ κ (wk⟦⟧ⁿᶠ ι xˢ)
  wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ {xˢ = neˢᵉᵐ xˢ}  = cong neˢᵉᵐ wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ
  wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ {xˢ = ƛˢᵉᵐ bˢ ρ} = cong (ƛˢᵉᵐ bˢ) wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ

  wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} {xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧}
              -> wk⟦⟧ⁿᵉ (κ ∘ᵒᵖᵉ ι) xˢ ≡ wk⟦⟧ⁿᵉ κ (wk⟦⟧ⁿᵉ ι xˢ)
  wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ {κ = κ} {ι} {xˢ = var v}   = cong var (wk⟦⟧ᵛᵃʳ-∘ᵒᵖᵉ κ ι v)
  wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ             {xˢ = fˢ ∙ xˢ} = cong₂ _∙_ wk⟦⟧ⁿᵉ-∘ᵒᵖᵉ wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ

  wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ : ∀ {Γ Δ Θ Ξ} {κ : Θ ⊆ Ξ} {ι : Δ ⊆ Θ} {ρ : ⟦ Γ ↦ Δ ⟧}
               -> wk⟦⟧ᵉⁿᵛ (κ ∘ᵒᵖᵉ ι) ρ ≡ wk⟦⟧ᵉⁿᵛ κ (wk⟦⟧ᵉⁿᵛ ι ρ)
  wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ {ρ =  εᵉⁿᵛ    } = refl
  wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ {ρ = ρ ▻ᵉⁿᵛ xˢ} = cong₂ _▻ᵉⁿᵛ_ wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ

wk-$⇓ : ∀ {Γ Δ σ τ} {ι : Γ ⊆ Δ} {fˢ : ⟦ Γ ⊢ⁿᶠ σ ⇒ τ ⟧} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧} {yˢ : ⟦ Γ ⊢ⁿᶠ τ ⟧}
      -> fˢ $ xˢ ⇓ yˢ -> wk⟦⟧ⁿᶠ ι fˢ $ wk⟦⟧ⁿᶠ ι xˢ ⇓ wk⟦⟧ⁿᶠ ι yˢ 
wk-$⇓  ne$⇓    = ne$⇓
wk-$⇓ (ƛ$⇓ qb) = ƛ$⇓ {!!}

mutual
  wk-Quoteⁿᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} {xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧} {xʳ : Γ ⊢ⁿᵉ σ}
             -> Quoteⁿᵉ xˢ ⇓ xʳ -> Quoteⁿᵉ wk⟦⟧ⁿᵉ ι xˢ ⇓ wkⁿᵉ ι xʳ
  wk-Quoteⁿᵉ  var⇓      = var⇓
  wk-Quoteⁿᵉ (qf ∙⇓ qx) = wk-Quoteⁿᵉ qf ∙⇓ wk-Quoteⁿᶠ qx

  wk-Quoteⁿᶠ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧} {xʳ : Γ ⊢ⁿᶠ σ}
             -> Quoteⁿᶠ xˢ ⇓ xʳ -> Quoteⁿᶠ wk⟦⟧ⁿᶠ ι xˢ ⇓ wkⁿᶠ ι xʳ
  wk-Quoteⁿᶠ              (ne⇓ qx)    = ne⇓ (wk-Quoteⁿᵉ qx)
  wk-Quoteⁿᶠ {ι = ι} {xˢ} (ƛ⇓_ qy qb) = ƛ⇓_ (coerce qy) (wk-Quoteⁿᶠ qb) where
    proof  = trans (sym wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ) (trans (cong (λ ι -> wk⟦⟧ⁿᶠ (skip ι) _) {!!}) wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ)
    coerce = subst (_$ _ ⇓ _) proof ∘ wk-$⇓
    
wkˢᶜᵛ : ∀ {Γ Δ σ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧}
      -> (ι : Γ ⊆ Δ) -> SCV xˢ -> SCV (wk⟦⟧ⁿᶠ ι xˢ)
wkˢᶜᵛ {σ = ⋆}     {neˢᵉᵐ xˢ} ι (x , qx) = wkⁿᵉ ι x , wk-Quoteⁿᵉ qx
wkˢᶜᵛ {σ = σ ⇒ τ}            ι  r       = λ κ xˢᶜᵛ ->
  case r (κ ∘ᵒᵖᵉ ι) xˢᶜᵛ of λ{
    (yˢ , yʳ , yˢᶜᵛ) -> yˢ , subst (_$ _ ⇓ yˢ) wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ yʳ , yˢᶜᵛ
  }
