open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product

open import Basic
open import Convertibility

∘idᵒᵖᵉ : ∀ {Γ Δ} {ι : Γ ⊆ Δ} -> ι ∘ᵒᵖᵉ idᵒᵖᵉ ≡ ι
∘idᵒᵖᵉ {ι = stop}   = refl
∘idᵒᵖᵉ {ι = skip ι} = cong skip ∘idᵒᵖᵉ
∘idᵒᵖᵉ {ι = keep ι} = cong keep ∘idᵒᵖᵉ

id∘ᵒᵖᵉ : ∀ {Γ Δ} {ι : Γ ⊆ Δ} -> idᵒᵖᵉ ∘ᵒᵖᵉ ι ≡ ι
id∘ᵒᵖᵉ {ι = stop}   = refl
id∘ᵒᵖᵉ {ι = skip ι} = cong skip id∘ᵒᵖᵉ
id∘ᵒᵖᵉ {ι = keep ι} = cong keep id∘ᵒᵖᵉ

wk⟦⟧ᵛᵃʳ-idᵒᵖᵉ : ∀ {Γ σ} -> (v : σ ∈ Γ) -> wkᵛᵃʳ idᵒᵖᵉ v ≡ v
wk⟦⟧ᵛᵃʳ-idᵒᵖᵉ  vz    = refl
wk⟦⟧ᵛᵃʳ-idᵒᵖᵉ (vs v) = cong vs (wk⟦⟧ᵛᵃʳ-idᵒᵖᵉ v)

mutual
  wk⟦⟧ⁿᶠ-idᵒᵖᵉ : ∀ {Γ σ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧} -> wk⟦⟧ⁿᶠ idᵒᵖᵉ xˢ ≡ xˢ
  wk⟦⟧ⁿᶠ-idᵒᵖᵉ {xˢ = neˢᵉᵐ xˢ}  = cong neˢᵉᵐ wk⟦⟧ⁿᵉ-idᵒᵖᵉ
  wk⟦⟧ⁿᶠ-idᵒᵖᵉ {xˢ = ƛˢᵉᵐ bˢ ρ} = cong (ƛˢᵉᵐ bˢ) wk⟦⟧ᵉⁿᵛ-idᵒᵖᵉ

  wk⟦⟧ⁿᵉ-idᵒᵖᵉ : ∀ {Γ σ} {xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧} -> wk⟦⟧ⁿᵉ idᵒᵖᵉ xˢ ≡ xˢ
  wk⟦⟧ⁿᵉ-idᵒᵖᵉ {xˢ = var v}   = cong var (wk⟦⟧ᵛᵃʳ-idᵒᵖᵉ v)
  wk⟦⟧ⁿᵉ-idᵒᵖᵉ {xˢ = fˢ ∙ xˢ} = cong₂ _∙_ wk⟦⟧ⁿᵉ-idᵒᵖᵉ wk⟦⟧ⁿᶠ-idᵒᵖᵉ

  wk⟦⟧ᵉⁿᵛ-idᵒᵖᵉ : ∀ {Γ Δ} {ρ : ⟦ Γ ↦ Δ ⟧} -> wk⟦⟧ᵉⁿᵛ idᵒᵖᵉ ρ ≡ ρ
  wk⟦⟧ᵉⁿᵛ-idᵒᵖᵉ {ρ = εᵉⁿᵛ     } = refl
  wk⟦⟧ᵉⁿᵛ-idᵒᵖᵉ {ρ = ρ ▻ᵉⁿᵛ xˢ} = cong₂ _▻ᵉⁿᵛ_ wk⟦⟧ᵉⁿᵛ-idᵒᵖᵉ wk⟦⟧ⁿᶠ-idᵒᵖᵉ

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
  wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ {ρ = εᵉⁿᵛ     } = refl
  wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ {ρ = ρ ▻ᵉⁿᵛ xˢ} = cong₂ _▻ᵉⁿᵛ_ wk⟦⟧ᵉⁿᵛ-∘ᵒᵖᵉ wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ

postulate
  ≈-emb⟦⟧ⁿᵉ-wkⁿᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧) (x : Γ ⊢ⁿᵉ σ)
                 -> emb⟦⟧ⁿᵉ xˢ ≈ embⁿᵉ x
                 -> emb⟦⟧ⁿᵉ (wk⟦⟧ⁿᵉ ι xˢ) ≈ embⁿᵉ (wkⁿᵉ ι x)
  ≈-emb⟦⟧ⁿᶠ-embᵒᵖᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧)
                   -> emb⟦⟧ⁿᶠ xˢ [ embᵒᵖᵉ ι ] ≈ emb⟦⟧ⁿᶠ (wk⟦⟧ⁿᶠ ι xˢ)
