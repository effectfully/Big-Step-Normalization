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

embᵒᵖᵉ-∘ˢᵘᵇ-ε↦ : ∀ {Γ Δ} {ψ : Γ ↦ Δ} -> ψ ∘ˢᵘᵇ ε↦ ≈ˢ ε↦
embᵒᵖᵉ-∘ˢᵘᵇ-ε↦ {ψ = idˢᵘᵇ   } = ≈ˢ-idˡ
embᵒᵖᵉ-∘ˢᵘᵇ-ε↦ {ψ = ↑       } = ≈ˢ-refl
embᵒᵖᵉ-∘ˢᵘᵇ-ε↦ {ψ = ψ ▻ˢᵘᵇ x} =
  ≈ˢ-trans ≈ˢ-assoc (≈ˢ-trans (≈ˢ∘-cong ≈ˢ∘↑ ≈ˢ-refl) embᵒᵖᵉ-∘ˢᵘᵇ-ε↦)
embᵒᵖᵉ-∘ˢᵘᵇ-ε↦ {ψ = φ ∘ˢᵘᵇ ψ} =
  ≈ˢ-trans (≈ˢ-sym ≈ˢ-assoc) (≈ˢ-trans (≈ˢ∘-cong ≈ˢ-refl embᵒᵖᵉ-∘ˢᵘᵇ-ε↦) embᵒᵖᵉ-∘ˢᵘᵇ-ε↦)

emb⟦⟧ᵒᵖᵉ-idᵒᵖᵉ : ∀ {Γ} -> idˢᵘᵇ {Γ} ≈ˢ embᵒᵖᵉ idᵒᵖᵉ
emb⟦⟧ᵒᵖᵉ-idᵒᵖᵉ {ε}     = ≈ˢ-refl
emb⟦⟧ᵒᵖᵉ-idᵒᵖᵉ {Γ ▻ σ} =
  ≈ˢ-trans ≈ˢ▻-id (≈ˢ▻-cong (≈ˢ∘-cong ≈ˢ-refl emb⟦⟧ᵒᵖᵉ-idᵒᵖᵉ) ≈-refl)

≈-emb⟦⟧ᵛᵃʳ-embᵒᵖᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (v : σ ∈ Γ)
                  -> embᵛᵃʳ v [ embᵒᵖᵉ ι ] ≈ embᵛᵃʳ (wkᵛᵃʳ ι v)
≈-emb⟦⟧ᵛᵃʳ-embᵒᵖᵉ {ι = stop  } ()
≈-emb⟦⟧ᵛᵃʳ-embᵒᵖᵉ {ι = skip ι}  v     =
  ≈-trans (≈-sym ≈[]∘) (≈[]-cong (≈-emb⟦⟧ᵛᵃʳ-embᵒᵖᵉ v) ≈ˢ-refl)
≈-emb⟦⟧ᵛᵃʳ-embᵒᵖᵉ {ι = keep ι}  vz    = ≈ø
≈-emb⟦⟧ᵛᵃʳ-embᵒᵖᵉ {ι = keep ι} (vs v) =
  ≈-trans (≈-trans (≈-trans ≈[]∘ (≈[]-cong ≈-refl ≈ˢ∘↑))
    (≈-sym ≈[]∘)) (≈[]-cong (≈-emb⟦⟧ᵛᵃʳ-embᵒᵖᵉ v) ≈ˢ-refl)

mutual
  ≈-emb⟦⟧ⁿᶠ-embᵒᵖᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧)
                   -> emb⟦⟧ⁿᶠ xˢ [ embᵒᵖᵉ ι ] ≈ emb⟦⟧ⁿᶠ (wk⟦⟧ⁿᶠ ι xˢ)
  ≈-emb⟦⟧ⁿᶠ-embᵒᵖᵉ (neˢᵉᵐ xˢ)  = ≈-emb⟦⟧ⁿᵉ-embᵒᵖᵉ xˢ
  ≈-emb⟦⟧ⁿᶠ-embᵒᵖᵉ (ƛˢᵉᵐ bˢ ρ) =
    ≈-trans ≈[]∘ (≈[]-cong ≈-refl (≈-emb⟦⟧ᵉⁿᵛ-embᵒᵖᵉ ρ))

  ≈-emb⟦⟧ⁿᵉ-embᵒᵖᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧)
                   -> emb⟦⟧ⁿᵉ xˢ [ embᵒᵖᵉ ι ] ≈ emb⟦⟧ⁿᵉ (wk⟦⟧ⁿᵉ ι xˢ)
  ≈-emb⟦⟧ⁿᵉ-embᵒᵖᵉ (var v)   = ≈-emb⟦⟧ᵛᵃʳ-embᵒᵖᵉ v
  ≈-emb⟦⟧ⁿᵉ-embᵒᵖᵉ (fˢ ∙ xˢ) =
    ≈-trans ≈∙[] (≈∙-cong (≈-emb⟦⟧ⁿᵉ-embᵒᵖᵉ fˢ) (≈-emb⟦⟧ⁿᶠ-embᵒᵖᵉ xˢ))

  ≈-emb⟦⟧ᵉⁿᵛ-embᵒᵖᵉ : ∀ {Γ Δ Θ} {ι : Δ ⊆ Θ} (ρ : ⟦ Γ ↦ Δ ⟧)
                    -> embᵒᵖᵉ ι ∘ˢᵘᵇ emb⟦⟧ᵉⁿᵛ ρ ≈ˢ emb⟦⟧ᵉⁿᵛ (wk⟦⟧ᵉⁿᵛ ι ρ)
  ≈-emb⟦⟧ᵉⁿᵛ-embᵒᵖᵉ  εᵉⁿᵛ       = embᵒᵖᵉ-∘ˢᵘᵇ-ε↦
  ≈-emb⟦⟧ᵉⁿᵛ-embᵒᵖᵉ (ρ ▻ᵉⁿᵛ xˢ) =
    ≈ˢ-trans ≈ˢ∘▻ (≈ˢ▻-cong (≈-emb⟦⟧ᵉⁿᵛ-embᵒᵖᵉ ρ) (≈-emb⟦⟧ⁿᶠ-embᵒᵖᵉ xˢ))

emb⟦⟧ᵉⁿᵛ-idᵉⁿᵛ : ∀ {Γ} -> idˢᵘᵇ {Γ} ≈ˢ emb⟦⟧ᵉⁿᵛ idᵉⁿᵛ
emb⟦⟧ᵉⁿᵛ-idᵉⁿᵛ {ε}     = ≈ˢ-refl
emb⟦⟧ᵉⁿᵛ-idᵉⁿᵛ {Γ ▻ σ} =
  ≈ˢ-trans ≈ˢ▻-id (≈ˢ▻-cong (≈ˢ-trans
    (≈ˢ∘-cong (≈ˢ-trans (≈ˢ-sym ≈ˢ-idʳ)
      (≈ˢ∘-cong ≈ˢ-refl emb⟦⟧ᵒᵖᵉ-idᵒᵖᵉ)) emb⟦⟧ᵉⁿᵛ-idᵉⁿᵛ)
        (≈-emb⟦⟧ᵉⁿᵛ-embᵒᵖᵉ idᵉⁿᵛ)) ≈-refl)

mutual
  ≈-embⁿᶠ-embᵒᵖᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (xˢ : Γ ⊢ⁿᶠ σ)
                 -> embⁿᶠ xˢ [ embᵒᵖᵉ ι ] ≈ embⁿᶠ (wkⁿᶠ ι xˢ)
  ≈-embⁿᶠ-embᵒᵖᵉ (neⁿᶠ xˢ) = ≈-embⁿᵉ-embᵒᵖᵉ xˢ
  ≈-embⁿᶠ-embᵒᵖᵉ (ƛⁿᶠ bˢ)  = ≈-trans ≈ƛ[] (≈ƛ-cong (≈-embⁿᶠ-embᵒᵖᵉ bˢ))

  ≈-embⁿᵉ-embᵒᵖᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (xˢ : Γ ⊢ⁿᵉ σ)
                 -> embⁿᵉ xˢ [ embᵒᵖᵉ ι ] ≈ embⁿᵉ (wkⁿᵉ ι xˢ)
  ≈-embⁿᵉ-embᵒᵖᵉ (var v)   = ≈-emb⟦⟧ᵛᵃʳ-embᵒᵖᵉ v
  ≈-embⁿᵉ-embᵒᵖᵉ (fˢ ∙ xˢ) =
    ≈-trans ≈∙[] (≈∙-cong (≈-embⁿᵉ-embᵒᵖᵉ fˢ) (≈-embⁿᶠ-embᵒᵖᵉ xˢ))

≈-emb⟦⟧ⁿᵉ-wkⁿᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧) (x : Γ ⊢ⁿᵉ σ)
               -> emb⟦⟧ⁿᵉ xˢ ≈ embⁿᵉ x
               -> emb⟦⟧ⁿᵉ (wk⟦⟧ⁿᵉ ι xˢ) ≈ embⁿᵉ (wkⁿᵉ ι x)
≈-emb⟦⟧ⁿᵉ-wkⁿᵉ xˢ x eq =
  ≈-trans (≈-trans (≈-sym (≈-emb⟦⟧ⁿᵉ-embᵒᵖᵉ xˢ)) (≈[]-cong eq ≈ˢ-refl)) (≈-embⁿᵉ-embᵒᵖᵉ x)
