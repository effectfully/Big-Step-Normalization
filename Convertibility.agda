open import Basic

infix 4 _≈_ _≈ˢ_


mutual
  data _≈_ : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ -> Set where
    ≈-refl   : ∀ {Γ σ} {x     : Γ ⊢ σ} -> x ≈ x
    ≈-sym    : ∀ {Γ σ} {x y   : Γ ⊢ σ} -> x ≈ y -> y ≈ x
    ≈-trans  : ∀ {Γ σ} {x y z : Γ ⊢ σ} -> x ≈ y -> y ≈ z -> x ≈ z
    ≈ƛ-cong  : ∀ {Γ σ τ} {b d : Γ ▻ σ ⊢ τ}
             -> b ≈ d -> (ƛ b) ≈ (ƛ d)
    ≈∙-cong  : ∀ {Γ σ τ} {f g : Γ ⊢ σ ⇒ τ} {x y : Γ ⊢ σ}
             -> f ≈ g -> x ≈ y -> f ∙ x ≈ g ∙ y
    ≈[]-cong : ∀ {Γ Δ σ} {x y : Γ ⊢ σ} {ψ φ : Γ ↦ Δ}
             -> x ≈ y -> ψ ≈ˢ φ -> x [ ψ ] ≈ y [ φ ]
    ≈ø       : ∀ {Γ Δ σ} {x : Δ ⊢ σ} {ψ : Γ ↦ Δ}
             -> ø [ ψ ▻ˢᵘᵇ x ] ≈ x
    ≈-id     : ∀ {Γ σ} {x : Γ ⊢ σ}
             -> x ≈ x [ idˢᵘᵇ ]
    ≈[]∘     : ∀ {Γ Δ Θ σ} {x : Γ ⊢ σ} {φ : Δ ↦ Θ} {ψ : Γ ↦ Δ}
             -> x [ ψ ] [ φ ] ≈ x [ φ ∘ˢᵘᵇ ψ ]
    ≈ƛ[]     : ∀ {Γ Δ σ τ} {x : Γ ▻ σ ⊢ τ} {ψ : Γ ↦ Δ}
             -> (ƛ x) [ ψ ] ≈ (ƛ x [ ↑ ∘ˢᵘᵇ ψ ▻ˢᵘᵇ ø ])
    ≈∙[]     : ∀ {Γ Δ σ τ} {f : Γ ⊢ σ ⇒ τ} {x : Γ ⊢ σ} {ψ : Γ ↦ Δ}
             -> (f ∙ x) [ ψ ] ≈ f [ ψ ] ∙ x [ ψ ]
    ≈βσ      : ∀ {Γ Δ σ τ} {b : Γ ▻ σ ⊢ τ} {x : Δ ⊢ σ} {ψ : Γ ↦ Δ}
             -> (ƛ b) [ ψ ] ∙ x ≈ b [ ψ ▻ˢᵘᵇ x ]
    ≈η       : ∀ {Γ σ τ} {x : Γ ⊢ σ ⇒ τ}
             -> x ≈ (ƛ (x [ ↑ ] ∙ ø))

  data _≈ˢ_ : ∀ {Γ Δ} -> Γ ↦ Δ -> Γ ↦ Δ -> Set where
    ≈ˢ-refl  : ∀ {Γ Δ} {ψ     : Γ ↦ Δ} -> ψ ≈ˢ ψ
    ≈ˢ-sym   : ∀ {Γ Δ} {ψ φ   : Γ ↦ Δ} -> ψ ≈ˢ φ -> φ ≈ˢ ψ
    ≈ˢ-trans : ∀ {Γ Δ} {ψ φ χ : Γ ↦ Δ} -> ψ ≈ˢ φ -> φ ≈ˢ χ -> ψ ≈ˢ χ
    ≈ˢ∘-cong : ∀ {Γ Δ Θ} {φ₁ φ₂ : Δ ↦ Θ} {ψ₁ ψ₂ : Γ ↦ Δ}
             -> φ₁ ≈ˢ φ₂ -> ψ₁ ≈ˢ ψ₂ -> φ₁ ∘ˢᵘᵇ ψ₁ ≈ˢ φ₂ ∘ˢᵘᵇ ψ₂
    ≈ˢ▻-cong : ∀ {Γ Δ σ} {x y : Δ ⊢ σ} {ψ φ : Γ ↦ Δ}
             -> ψ ≈ˢ φ -> x ≈ y -> ψ ▻ˢᵘᵇ x ≈ˢ φ ▻ˢᵘᵇ y
    ≈ˢ-assoc : ∀ {Γ Δ Θ Ξ} {χ : Θ ↦ Ξ} {φ : Δ ↦ Θ} {ψ : Γ ↦ Δ}
             -> χ ∘ˢᵘᵇ (φ ∘ˢᵘᵇ ψ) ≈ˢ (χ ∘ˢᵘᵇ φ) ∘ˢᵘᵇ ψ
    ≈ˢ-idˡ   : ∀ {Γ Δ} {ψ : Γ ↦ Δ}
             -> idˢᵘᵇ ∘ˢᵘᵇ ψ ≈ˢ ψ
    ≈ˢ-idʳ   : ∀ {Γ Δ} {ψ : Γ ↦ Δ}
             -> ψ ∘ˢᵘᵇ idˢᵘᵇ ≈ˢ ψ 
    ≈ˢ∘↑     : ∀ {Γ Δ σ} {x : Δ ⊢ σ} {ψ : Γ ↦ Δ}
             -> (ψ ▻ˢᵘᵇ x) ∘ˢᵘᵇ ↑ ≈ˢ ψ
    ≈ˢ∘▻     : ∀ {Γ Δ Θ σ} {x : Δ ⊢ σ} {φ : Δ ↦ Θ} {ψ : Γ ↦ Δ}
             -> φ ∘ˢᵘᵇ (ψ ▻ˢᵘᵇ x) ≈ˢ φ ∘ˢᵘᵇ ψ ▻ˢᵘᵇ x [ φ ]
    ≈ˢ▻-id   : ∀ {Γ σ}
             -> idˢᵘᵇ {Γ ▻ σ} ≈ˢ ↑ ∘ˢᵘᵇ idˢᵘᵇ ▻ˢᵘᵇ ø
