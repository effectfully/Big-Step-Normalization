open import Function hiding (_$_)
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Basic
open import BigStep
open import SCV

∘idᵒᵖᵉ : ∀ {Γ Δ} {ι : Γ ⊆ Δ} -> ι ∘ᵒᵖᵉ idᵒᵖᵉ ≡ ι
∘idᵒᵖᵉ {ι = stop}   = refl
∘idᵒᵖᵉ {ι = skip ι} = cong skip ∘idᵒᵖᵉ
∘idᵒᵖᵉ {ι = keep ι} = cong keep ∘idᵒᵖᵉ

id∘ᵒᵖᵉ : ∀ {Γ Δ} {ι : Γ ⊆ Δ} -> idᵒᵖᵉ ∘ᵒᵖᵉ ι ≡ ι
id∘ᵒᵖᵉ {ι = stop}   = refl
id∘ᵒᵖᵉ {ι = skip ι} = cong skip id∘ᵒᵖᵉ
id∘ᵒᵖᵉ {ι = keep ι} = cong keep id∘ᵒᵖᵉ

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

mutual
  wk-⟦⟧⇓ : ∀ {Γ Δ Θ σ} {ι : Δ ⊆ Θ} {x : Γ ⊢ σ} {xˢʳ : ⟦ Δ ⊢ⁿᶠ σ ⟧} {ρ : ⟦ Γ ↦ Δ ⟧}
         -> ⟦ x ⟧ ρ ⇓ xˢʳ -> ⟦ x ⟧ wk⟦⟧ᵉⁿᵛ ι ρ ⇓ wk⟦⟧ⁿᶠ ι xˢʳ
  wk-⟦⟧⇓  ø⇓              = ø⇓
  wk-⟦⟧⇓  ƛ⇓_             = ƛ⇓_
  wk-⟦⟧⇓ (ef ∙⟨ ey ⟩⇓ ex) = wk-⟦⟧⇓ ef ∙⟨ wk-$⇓ ey ⟩⇓ wk-⟦⟧⇓ ex
  wk-⟦⟧⇓ (eb [ eψ ]⇓)     = wk-⟦⟧⇓ eb [ wk-⟦⟧ˢᵘᵇ⇓ eψ ]⇓

  wk-⟦⟧ˢᵘᵇ⇓ : ∀ {Γ Δ Θ Ξ} {ι : Θ ⊆ Ξ} {ψ : Γ ↦ Δ} {ρ : ⟦ Δ ↦ Θ ⟧} {ρʳ : ⟦ Γ ↦ Θ ⟧}
            -> ⟦ ψ ⟧ˢᵘᵇ ρ ⇓ ρʳ -> ⟦ ψ ⟧ˢᵘᵇ wk⟦⟧ᵉⁿᵛ ι ρ ⇓ wk⟦⟧ᵉⁿᵛ ι ρʳ
  wk-⟦⟧ˢᵘᵇ⇓  idˢᵘᵇ⇓       = idˢᵘᵇ⇓
  wk-⟦⟧ˢᵘᵇ⇓  ↑⇓           = ↑⇓
  wk-⟦⟧ˢᵘᵇ⇓ (eψ ▻ˢᵘᵇ⇓ ex) = wk-⟦⟧ˢᵘᵇ⇓ eψ ▻ˢᵘᵇ⇓ wk-⟦⟧⇓ ex
  wk-⟦⟧ˢᵘᵇ⇓ (eψ ∘ˢᵘᵇ⇓ eφ) = wk-⟦⟧ˢᵘᵇ⇓ eψ ∘ˢᵘᵇ⇓ wk-⟦⟧ˢᵘᵇ⇓ eφ

  wk-$⇓ : ∀ {Γ Δ σ τ} {ι : Γ ⊆ Δ} {fˢ : ⟦ Γ ⊢ⁿᶠ σ ⇒ τ ⟧} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧} {yˢ : ⟦ Γ ⊢ⁿᶠ τ ⟧}
        -> fˢ $ xˢ ⇓ yˢ -> wk⟦⟧ⁿᶠ ι fˢ $ wk⟦⟧ⁿᶠ ι xˢ ⇓ wk⟦⟧ⁿᶠ ι yˢ 
  wk-$⇓  ne$⇓    = ne$⇓
  wk-$⇓ (ƛ$⇓ eb) = ƛ$⇓ (wk-⟦⟧⇓ eb)

mutual
  wk-Quoteⁿᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} {xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧} {xʳ : Γ ⊢ⁿᵉ σ}
             -> Quoteⁿᵉ xˢ ⇓ xʳ -> Quoteⁿᵉ wk⟦⟧ⁿᵉ ι xˢ ⇓ wkⁿᵉ ι xʳ
  wk-Quoteⁿᵉ  var⇓      = var⇓
  wk-Quoteⁿᵉ (qf ∙⇓ qx) = wk-Quoteⁿᵉ qf ∙⇓ wk-Quoteⁿᶠ qx

  wk-Quoteⁿᶠ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧} {xʳ : Γ ⊢ⁿᶠ σ}
             -> Quoteⁿᶠ xˢ ⇓ xʳ -> Quoteⁿᶠ wk⟦⟧ⁿᶠ ι xˢ ⇓ wkⁿᶠ ι xʳ
  wk-Quoteⁿᶠ              (ne⇓ qx)    = ne⇓ (wk-Quoteⁿᵉ qx)
  wk-Quoteⁿᶠ {ι = ι} {xˢ} (ƛ⇓_ qy qb) = ƛ⇓_ (coerce (wk-$⇓ qy)) (wk-Quoteⁿᶠ qb) where
    coerce = subst (_$ _ ⇓ _)
               (trans (sym wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ)
                  (trans (cong (λ ι -> wk⟦⟧ⁿᶠ (skip ι) _)
                     (trans ∘idᵒᵖᵉ (sym id∘ᵒᵖᵉ))) wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ))
    
wkˢᶜᵛ : ∀ {Γ Δ σ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧} {ι : Γ ⊆ Δ}
      -> SCV xˢ -> SCV (wk⟦⟧ⁿᶠ ι xˢ)
wkˢᶜᵛ {σ = ⋆}     {neˢᵉᵐ xˢ} (x , qx) = wkⁿᵉ _ x , wk-Quoteⁿᵉ qx
wkˢᶜᵛ {σ = σ ⇒ τ}             r       = λ κ xˢᶜᵛ ->
  case r (κ ∘ᵒᵖᵉ _) xˢᶜᵛ of λ{
    (yˢ , yʳ , yˢᶜᵛ) -> yˢ , subst (_$ _ ⇓ yˢ) wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ yʳ , yˢᶜᵛ
  }

wkˢᶜᵉ : ∀ {Γ Δ Θ} {ι : Δ ⊆ Θ} {ρ : ⟦ Γ ↦ Δ ⟧} -> SCE ρ -> SCE (wk⟦⟧ᵉⁿᵛ ι ρ)
wkˢᶜᵉ  εˢᶜᵉ         = εˢᶜᵉ
wkˢᶜᵉ (ρ ▻ˢᶜᵉ xˢᶜᵛ) = wkˢᶜᵉ ρ ▻ˢᶜᵉ wkˢᶜᵛ xˢᶜᵛ

mutual
  quoteˢᶜᵛ : ∀ {Γ σ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧}
           -> SCV xˢ -> ∃ λ (xʳ : Γ ⊢ⁿᶠ σ) -> Quoteⁿᶠ xˢ ⇓ xʳ
  quoteˢᶜᵛ {σ = ⋆}     {neˢᵉᵐ xˢ} (x , qx) = neⁿᶠ x , ne⇓ qx
  quoteˢᶜᵛ {σ = σ ⇒ τ}             r       =
    case r topᵒᵖᵉ (unquoteˢᶜᵛ var⇓) of λ{
      (bˢ̂ʳ , ay , bˢᶜᵛ) -> case quoteˢᶜᵛ bˢᶜᵛ of λ{
        (b , qb) -> (ƛⁿᶠ b) , ƛ⇓_ ay qb
      }
    }

  unquoteˢᶜᵛ : ∀ {Γ σ} {xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧} {xʳ}
             -> Quoteⁿᵉ xˢ ⇓ xʳ -> SCV (neˢᵉᵐ xˢ)
  unquoteˢᶜᵛ {σ = ⋆}     qx = _ , qx
  unquoteˢᶜᵛ {σ = σ ⇒ τ} qf = λ ι xˢᶜᵛ -> case quoteˢᶜᵛ xˢᶜᵛ of λ{
      (x , qx) -> _ , ne$⇓ , unquoteˢᶜᵛ (wk-Quoteⁿᵉ qf ∙⇓ qx)
    }

varˢᶜᵛ : ∀ {Γ σ} -> (v : σ ∈ Γ) -> SCV (varˢᵉᵐ v)
varˢᶜᵛ v = unquoteˢᶜᵛ var⇓

idˢᶜᵉ : ∀ {Γ} -> SCE (idᵉⁿᵛ {Γ})
idˢᶜᵉ {ε}     = εˢᶜᵉ
idˢᶜᵉ {Γ ▻ σ} = wkˢᶜᵉ idˢᶜᵉ ▻ˢᶜᵉ varˢᶜᵛ vz
