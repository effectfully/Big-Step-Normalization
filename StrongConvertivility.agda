open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Basic
open import BigStep
open import Structural

_~_ : ∀ {σ Γ} -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> Set
_~_ {⋆}         (neˢᵉᵐ x) (neˢᵉᵐ y) =
  ∀ {xʳ yʳ p₁ p₂} -> proj₁ (quoteⁿᵉ x {xʳ} p₁) ≡ proj₁ (quoteⁿᵉ y {yʳ} p₂)
_~_ {σ ⇒ τ} {Γ}  f         g        =
  ∀ {Δ} {x y} (ι : Γ ⊆ Δ) {x' y' p₁ p₂}
    -> x ~ y -> proj₁ (evalᵃᵖᵖ (wk⟦⟧ⁿᶠ ι f) x {x'} p₁) ~ proj₁ (evalᵃᵖᵖ (wk⟦⟧ⁿᶠ ι g) y {y'} p₂)

data _~ᵉⁿᵛ_ {Δ} : ∀ {Γ} -> ⟦ Γ ↦ Δ ⟧ -> ⟦ Γ ↦ Δ ⟧ -> Set where
  ~ε : εᵉⁿᵛ ~ᵉⁿᵛ εᵉⁿᵛ
  ~▻ : ∀ {Γ σ} {ρ₁ ρ₂ : ⟦ Γ ↦ Δ ⟧} {x₁ x₂ : ⟦ Δ ⊢ⁿᶠ σ ⟧} 
     -> ρ₁ ~ᵉⁿᵛ ρ₂ -> x₁ ~ x₂ -> (ρ₁ ▻ᵉⁿᵛ x₁) ~ᵉⁿᵛ (ρ₂ ▻ᵉⁿᵛ x₂)

postulate
  wk~ : ∀ {Γ Δ σ} {x y : ⟦ Γ ⊢ⁿᶠ σ ⟧} {ι : Γ ⊆ Δ} -> x ~ y -> wk⟦⟧ⁿᶠ ι x ~ wk⟦⟧ⁿᶠ ι y
  wk~ᵉⁿᵛ : ∀ {Γ Δ Θ} {ι : Δ ⊆ Θ} {ρ₁ ρ₂ : ⟦ Γ ↦ Δ ⟧} -> ρ₁ ~ᵉⁿᵛ ρ₂ -> wk⟦⟧ᵉⁿᵛ ι ρ₁ ~ᵉⁿᵛ wk⟦⟧ᵉⁿᵛ ι ρ₂
  sym~ : ∀ {Γ σ} {x y : ⟦ Γ ⊢ⁿᶠ σ ⟧} -> x ~ y -> y ~ x
  trans~ : ∀ {Γ σ} {x y z : ⟦ Γ ⊢ⁿᶠ σ ⟧} -> x ~ y -> y ~ z -> x ~ z

quoteⁿᵉ-lem : ∀ {σ Γ} {xʳ yʳ} p₁ p₂
            -> proj₁ (quoteⁿᵉ {Γ ▻ σ} (var vz) {xʳ} p₁) ≡ proj₁ (quoteⁿᵉ (var vz) {yʳ} p₂)
quoteⁿᵉ-lem var⇓ var⇓ = refl

mutual
  quoteⁿᶠ~ : ∀ {σ Γ} {xʳ yʳ} (x y : ⟦ Γ ⊢ⁿᶠ σ ⟧) p₁ p₂
           -> x ~ y -> proj₁ (quoteⁿᶠ σ x {xʳ} p₁) ≡ proj₁ (quoteⁿᶠ σ y {yʳ} p₂)
  quoteⁿᶠ~ {⋆}     (neˢᵉᵐ x) (neˢᵉᵐ y) (ne⇓ ex)      (ne⇓ ey)      q
    with quoteⁿᵉ x ex | quoteⁿᵉ y ey | q {p₁ = ex} {p₂ = ey}
  ... | x' , refl | y' , refl | q' = cong neⁿᶠ q'
  quoteⁿᶠ~ {σ ⇒ τ}  f         g        (ƛ⇓_ ax₁ qx₁) (ƛ⇓_ ax₂ qx₂) q
    with evalᵃᵖᵖ (wk⟦⟧ⁿᶠ topᵒᵖᵉ f) (varˢᵉᵐ vz) ax₁
       | evalᵃᵖᵖ (wk⟦⟧ⁿᶠ topᵒᵖᵉ g) (varˢᵉᵐ vz) ax₂
       | q {x = varˢᵉᵐ vz} {varˢᵉᵐ vz} topᵒᵖᵉ {p₁ = ax₁} {p₂ = ax₂}
             (quoteⁿᵉ~ (var {σ = σ} vz) (var {σ = σ} vz) (λ {x y p₁ p₂} -> quoteⁿᵉ-lem p₁ p₂))
  ... | b₁ , refl | b₂ , refl | e
    with quoteⁿᶠ τ b₁ qx₁ | quoteⁿᶠ τ b₂ qx₂ | quoteⁿᶠ~ b₁ b₂ qx₁ qx₂ e
  ... | b₁' , refl | b₂' , refl | r = cong ƛⁿᶠ_ r

  quoteⁿᵉ~ : ∀ {σ Γ} (x y : ⟦ Γ ⊢ⁿᵉ σ ⟧)
           -> (∀ {xʳ yʳ p₁ p₂} -> proj₁ (quoteⁿᵉ x {xʳ} p₁) ≡ proj₁ (quoteⁿᵉ y {yʳ} p₂))
           -> neˢᵉᵐ x ~ neˢᵉᵐ y
  quoteⁿᵉ~ {⋆}     x y q       = q
  quoteⁿᵉ~ {σ ⇒ τ} x y q₁ ι q₂ = {!!}
