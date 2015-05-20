open import Function hiding (_$_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product

open import Basic
open import BigStep
open import Convertibility
open import Properties
open import SCV

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
wkˢᶜᵛ {σ = ⋆}     {neˢᵉᵐ xˢ} (x , qx , xˢ≈x) = wkⁿᵉ _ x , wk-Quoteⁿᵉ qx , ≈-emb⟦⟧ⁿᵉ-wkⁿᵉ xˢ x xˢ≈x
wkˢᶜᵛ {σ = σ ⇒ τ} {fˢ}        r              = λ κ xˢᶜᵛ ->
  case r (κ ∘ᵒᵖᵉ _) xˢᶜᵛ of λ{
    (yˢ , yʳ , yˢᶜᵛ , eq) -> yˢ , subst (_$ _ ⇓ yˢ) wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ yʳ , yˢᶜᵛ
        , subst (λ s -> emb⟦⟧ⁿᶠ s ∙ _ ≈ _) (wk⟦⟧ⁿᶠ-∘ᵒᵖᵉ {xˢ = fˢ}) eq
  }

wkˢᶜᵉ : ∀ {Γ Δ Θ} {ι : Δ ⊆ Θ} {ρ : ⟦ Γ ↦ Δ ⟧} -> SCE ρ -> SCE (wk⟦⟧ᵉⁿᵛ ι ρ)
wkˢᶜᵉ  εˢᶜᵉ         = εˢᶜᵉ
wkˢᶜᵉ (ρ ▻ˢᶜᵉ xˢᶜᵛ) = wkˢᶜᵉ ρ ▻ˢᶜᵉ wkˢᶜᵛ xˢᶜᵛ

mutual
  quoteˢᶜᵛ : ∀ {Γ σ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧}
           -> SCV xˢ -> ∃ λ (xʳ : Γ ⊢ⁿᶠ σ) -> Quoteⁿᶠ xˢ ⇓ xʳ × emb⟦⟧ⁿᶠ xˢ ≈ embⁿᶠ xʳ
  quoteˢᶜᵛ {σ = ⋆}     {neˢᵉᵐ xˢ} (x , qx , xˢ≈xʳ) = neⁿᶠ x , ne⇓ qx , xˢ≈xʳ
  quoteˢᶜᵛ {σ = σ ⇒ τ} {fˢ}        r               =
    case r topᵒᵖᵉ (unquoteˢᶜᵛ var⇓ ≈-refl) of λ{
      (bˢ̂ʳ , ay , bˢᶜᵛ , fˢ∙ø≈bˢʳ) -> case quoteˢᶜᵛ bˢᶜᵛ of λ{
        (b , qb , bˢ̂ʳ≈b) -> ƛⁿᶠ_ b , ƛ⇓_ ay qb ,
          ≈-trans ≈η
            (≈ƛ-cong
              (≈-trans
                (≈∙-cong
                  (≈-trans
                    (≈-trans
                      (≈[]-cong
                        (≈-trans
                          (subst (λ s -> emb⟦⟧ⁿᶠ fˢ ≈ emb⟦⟧ⁿᶠ s)
                                 (sym (wk⟦⟧ⁿᶠ-idᵒᵖᵉ {xˢ = fˢ}))
                                 (≈-refl {x = emb⟦⟧ⁿᶠ fˢ}))
                                 (≈-sym (≈-emb⟦⟧ⁿᶠ-embᵒᵖᵉ fˢ)))
                          ≈ˢ-refl)
                      ≈[]∘)
                    (≈-emb⟦⟧ⁿᶠ-embᵒᵖᵉ fˢ))
                  ≈-refl)
                (≈-trans fˢ∙ø≈bˢʳ bˢ̂ʳ≈b)))
      }
    }

  unquoteˢᶜᵛ : ∀ {Γ σ} {xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧} {xʳ}
             -> Quoteⁿᵉ xˢ ⇓ xʳ -> emb⟦⟧ⁿᵉ xˢ ≈ embⁿᵉ xʳ -> SCV (neˢᵉᵐ xˢ)
  unquoteˢᶜᵛ {σ = ⋆}                qx xˢ≈xʳ = _ , qx , xˢ≈xʳ
  unquoteˢᶜᵛ {σ = σ ⇒ τ} {fˢ} {fʳ}  qf fˢ≈fʳ = λ ι xˢᶜᵛ ->
    case quoteˢᶜᵛ xˢᶜᵛ of λ{
      (x , qx , xˢ≈xʳ) -> _
        , ne$⇓
        , unquoteˢᶜᵛ (wk-Quoteⁿᵉ qf ∙⇓ qx) (≈∙-cong (≈-emb⟦⟧ⁿᵉ-wkⁿᵉ fˢ fʳ fˢ≈fʳ) xˢ≈xʳ)
        , ≈-refl
    }

varˢᶜᵛ : ∀ {Γ σ} -> (v : σ ∈ Γ) -> SCV (varˢᵉᵐ v)
varˢᶜᵛ v = unquoteˢᶜᵛ var⇓ ≈-refl

idˢᶜᵉ : ∀ {Γ} -> SCE (idᵉⁿᵛ {Γ})
idˢᶜᵉ {ε}     = εˢᶜᵉ
idˢᶜᵉ {Γ ▻ σ} = wkˢᶜᵉ idˢᶜᵉ ▻ˢᶜᵉ varˢᶜᵛ vz

mutual
  ⟦_⟧& : ∀ {Γ Δ σ} {ρ : ⟦ Γ ↦ Δ ⟧} -> (x : Γ ⊢ σ) -> SCE ρ ->
    ∃ λ (xˢ : ⟦ Δ ⊢ⁿᶠ σ ⟧) -> ⟦ x ⟧ ρ ⇓ xˢ × SCV xˢ × x [ emb⟦⟧ᵉⁿᵛ ρ ] ≈ emb⟦⟧ⁿᶠ xˢ
  ⟦_⟧& {ρ = ρ ▻ᵉⁿᵛ _} ø (ρˢᶜᵉ ▻ˢᶜᵉ xˢᶜᵛ) = _ , ø⇓ , xˢᶜᵛ , ≈ø
  ⟦ ƛ b     ⟧& ρˢᶜᵉ = _ , ƛ⇓_ , (λ ι xˢᶜᵛ ->
    case ⟦ b ⟧& (wkˢᶜᵉ ρˢᶜᵉ ▻ˢᶜᵉ xˢᶜᵛ) of λ{
      (yˢ , eb , yˢᶜᵛ , eq₁) -> yˢ , (ƛ$⇓ eb) , yˢᶜᵛ , ≈-trans ≈βσ eq₁
    }) , ≈-refl
  ⟦ f ∙ x   ⟧& ρˢᶜᵉ =
    case ⟦ f ⟧& ρˢᶜᵉ , ⟦ x ⟧& ρˢᶜᵉ of λ{
      ((fˢ , ef , r , eq₁) , (xˢ , ex , xˢᶜᵛ , eq₂)) -> case r idᵒᵖᵉ xˢᶜᵛ of λ{
        (yˢ , ey , yˢᶜᵛ , eq₃) -> yˢ , (ef ∙⟨ subst (_$ _ ⇓ _) wk⟦⟧ⁿᶠ-idᵒᵖᵉ ey ⟩⇓ ex) , yˢᶜᵛ
          , ≈-trans (subst (λ s -> _ ≈ emb⟦⟧ⁿᶠ s ∙ _) (sym (wk⟦⟧ⁿᶠ-idᵒᵖᵉ {xˢ = fˢ}))
                       (≈-trans ≈∙[] (≈∙-cong eq₁ eq₂))) eq₃
      }
    }
  ⟦ x [ ψ ] ⟧& ρˢᶜᵉ =
    case ⟦ ψ ⟧ˢᵘᵇ& ρˢᶜᵉ of λ{
      (q , eq , qˢᶜᵉ , eq₁) -> case ⟦ x ⟧& qˢᶜᵉ of λ{
        (xˢ , ex , xˢᶜᵛ , eq₂) -> xˢ , (ex [ eq ]⇓) , xˢᶜᵛ
          , ≈-trans (≈-trans ≈[]∘ (≈[]-cong ≈-refl eq₁)) eq₂
      }
    }

  ⟦_⟧ˢᵘᵇ& : ∀ {Γ Δ Θ} {ρ : ⟦ Δ ↦ Θ ⟧} -> (ψ : Γ ↦ Δ) -> SCE ρ ->
    ∃ λ (ρˢ : ⟦ Γ ↦ Θ ⟧) -> ⟦ ψ ⟧ˢᵘᵇ ρ ⇓ ρˢ × SCE ρˢ × emb⟦⟧ᵉⁿᵛ ρ ∘ˢᵘᵇ ψ ≈ˢ emb⟦⟧ᵉⁿᵛ ρˢ
  ⟦ idˢᵘᵇ    ⟧ˢᵘᵇ& ρˢᶜᵉ = _ , idˢᵘᵇ⇓ , ρˢᶜᵉ , ≈ˢ-idʳ
  ⟦_⟧ˢᵘᵇ& {ρ = ρ ▻ᵉⁿᵛ _} ↑ (ρˢᶜᵉ ▻ˢᶜᵉ xˢᶜᵛ) = ρ , ↑⇓ , ρˢᶜᵉ , ≈ˢ∘↑
  ⟦ ψ ▻ˢᵘᵇ x ⟧ˢᵘᵇ& ρˢᶜᵉ =
    case ⟦ ψ ⟧ˢᵘᵇ& ρˢᶜᵉ , ⟦ x ⟧& ρˢᶜᵉ of λ{
      ((q , eq , qˢᶜᵉ , eq₁) , (xˢ , ex , xˢᶜᵛ , eq₂)) ->
        (q ▻ᵉⁿᵛ xˢ) , (eq ▻ˢᵘᵇ⇓ ex) , (qˢᶜᵉ ▻ˢᶜᵉ xˢᶜᵛ)
          , ≈ˢ-trans ≈ˢ∘▻ (≈ˢ▻-cong eq₁ eq₂)
    }
  ⟦ φ ∘ˢᵘᵇ ψ ⟧ˢᵘᵇ& ρˢᶜᵉ =
    case ⟦ φ ⟧ˢᵘᵇ& ρˢᶜᵉ of λ{
      (q , eq , qˢᶜᵉ , eq₁) -> case ⟦ ψ ⟧ˢᵘᵇ& qˢᶜᵉ of λ{
        (d , ed , dˢᶜᵉ , eq₂) -> d , (eq ∘ˢᵘᵇ⇓ ed) , dˢᶜᵉ
          , ≈ˢ-trans (≈ˢ-trans ≈ˢ-assoc (≈ˢ∘-cong eq₁ ≈ˢ-refl)) eq₂
      }
    }

∃-Norm : ∀ {Γ σ} -> (x : Γ ⊢ σ) -> ∃ λ xʳ -> Norm x ⇓ xʳ × x ≈ embⁿᶠ xʳ
∃-Norm x =
  case ⟦ x ⟧& idˢᶜᵉ of λ{
    (xˢʳ , ex , xˢᶜᵛ , eq₁) -> case quoteˢᶜᵛ xˢᶜᵛ of λ{
      (xʳ , qx , eq₂) -> xʳ , norm⇓ ex qx
        , ≈-trans (≈-trans (≈-trans ≈-id (≈[]-cong ≈-refl emb⟦⟧ᵉⁿᵛ-idᵉⁿᵛ)) eq₁) eq₂
    }
  }
