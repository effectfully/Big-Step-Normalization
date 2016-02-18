open import Function hiding (_$_)
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Basic
open import BigStep
open import Properties
open import SCV
open import Lemmas

mutual
  eval : ∀ {Γ Δ σ} (x : Γ ⊢ σ) (ρ : ⟦ Γ ↦ Δ ⟧) {xʳ}
       -> ⟦ x ⟧ ρ ⇓ xʳ -> ∃ (_≡ xʳ)
  eval  ø       (ρ ▻ᵉⁿᵛ x)  ø⇓              = x , refl
  eval (ƛ b)     ρ          ƛ⇓_             = ƛˢᵉᵐ b ρ , refl
  eval (f ∙ x)   ρ         (ef ∙⟨ ax ⟩⇓ ex) with eval f ρ ef | eval x ρ ex
  ... | f' , refl | x' , refl = evalᵃᵖᵖ f' x' ax
  eval (x [ ψ ]) ρ         (ex [ eψ ]⇓)     with evalˢᵘᵇ ψ ρ eψ
  ... | ρ' , refl = eval x ρ' ex

  evalᵃᵖᵖ : ∀ {Γ σ τ} (fˢ : ⟦ Γ ⊢ⁿᶠ σ ⇒ τ ⟧) (xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧) {yˢʳ}
          -> fˢ $ xˢ ⇓ yˢʳ -> ∃ (_≡ yˢʳ)
  evalᵃᵖᵖ (neˢᵉᵐ fˢ) xˢ  ne$⇓    = neˢᵉᵐ (fˢ ∙ xˢ) , refl
  evalᵃᵖᵖ (ƛˢᵉᵐ b ρ) xˢ (ƛ$⇓ eb) = eval b (ρ ▻ᵉⁿᵛ xˢ) eb

  evalˢᵘᵇ : ∀ {Γ Δ Θ} (ψ : Γ ↦ Δ) (ρ : ⟦ Δ ↦ Θ ⟧) {ρʳ}
          -> ⟦ ψ ⟧ˢᵘᵇ ρ ⇓ ρʳ -> ∃ (_≡ ρʳ)
  evalˢᵘᵇ  idˢᵘᵇ      ρ          idˢᵘᵇ⇓       = ρ , refl
  evalˢᵘᵇ  ↑         (ρ ▻ᵉⁿᵛ x)  ↑⇓           = ρ , refl
  evalˢᵘᵇ (ψ ▻ˢᵘᵇ x)  ρ         (eψ ▻ˢᵘᵇ⇓ ex) with evalˢᵘᵇ ψ ρ eψ | eval x ρ ex
  ... | ρ' , refl | x' , refl = ρ' ▻ᵉⁿᵛ x' , refl
  evalˢᵘᵇ (φ ∘ˢᵘᵇ ψ)  ρ         (eφ ∘ˢᵘᵇ⇓ eψ) with evalˢᵘᵇ φ ρ eφ
  ... | ρ' , refl = evalˢᵘᵇ ψ ρ' eψ

mutual
  quoteⁿᶠ : ∀ {Γ} σ (xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧) {xʳ} -> Quoteⁿᶠ xˢ ⇓ xʳ -> ∃ (_≡ xʳ)
  quoteⁿᶠ  ⋆      (neˢᵉᵐ x) (ne⇓ qx)    with quoteⁿᵉ x qx
  ... | x' , refl = neⁿᶠ x' , refl
  quoteⁿᶠ (σ ⇒ τ)  f        (ƛ⇓_ ax qx) with evalᵃᵖᵖ (wk⟦⟧ⁿᶠ topᵒᵖᵉ f) (varˢᵉᵐ vz) ax
  ... | b' , refl with quoteⁿᶠ τ b' qx
  ... | b'' , refl = (ƛⁿᶠ b'') , refl

  quoteⁿᵉ : ∀ {Γ σ} (xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧) {xʳ} -> Quoteⁿᵉ xˢ ⇓ xʳ -> ∃ (_≡ xʳ)
  quoteⁿᵉ (var v)  var⇓      = var v , refl
  quoteⁿᵉ (f ∙ x) (qf ∙⇓ qx) with quoteⁿᵉ f qf | quoteⁿᶠ _ x qx
  ... | f' , refl | x' , refl = f' ∙ x' , refl

norm : ∀ {Γ σ} {x : Γ ⊢ σ} {xʳ : Γ ⊢ⁿᶠ σ} -> Norm x ⇓ xʳ -> ∃ (_≡ xʳ)
norm (norm⇓ _ qx) = quoteⁿᶠ _ _ qx

nf : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ⁿᶠ σ
nf = proj₁ ∘ norm ∘ proj₁ ∘ proj₂ ∘ ∃-Norm
