open import Function hiding (_$_)
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Basic
open import BigStep
open import Properties
open import SCV
open import Lemmas

infixl 4 _<$>_ _<*>_

record Is {α} {A : Set α} (x : A) : Set α where
  ¡ = x
open Is

! : ∀ {α} {A : Set α} -> (x : A) -> Is x
! _ = _

_<$>_ : ∀ {α β} {A : Set α} {B : A -> Set β} {x}
      -> (f : ∀ x -> B x) -> Is x -> Is (f x)
_<$>_ = _

_<*>_ : ∀ {α β} {A : Set α} {B : A -> Set β} {f : ∀ x -> B x} {x}
      -> Is f -> Is x -> Is (f x)
_<*>_ = _

-- mutual
--   eval : ∀ {Γ Δ σ} {x : Γ ⊢ σ} {ρ : ⟦ Γ ↦ Δ ⟧} {xʳ} -> ⟦ x ⟧ ρ ⇓ xʳ -> Is xʳ
--   eval  ø⇓               = _
--   eval  ƛ⇓_              = _
--   eval (ef ∙⟨ ax ⟩⇓ ex)  = evalᵃᵖᵖ ax
--   eval (ex [ ψ ]⇓)       = eval ex

--   evalᵃᵖᵖ : ∀ {Γ σ τ} {fˢ : ⟦ Γ ⊢ⁿᶠ σ ⇒ τ ⟧} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧} {yˢʳ} -> fˢ $ xˢ ⇓ yˢʳ -> Is yˢʳ
--   evalᵃᵖᵖ  ne$⇓    = _
--   evalᵃᵖᵖ (ƛ$⇓ eb) = eval eb

--   evalˢᵘᵇ : ∀ {Γ Δ Θ} {ψ : Γ ↦ Δ} {ρ : ⟦ Δ ↦ Θ ⟧} {ρʳ} -> ⟦ ψ ⟧ˢᵘᵇ ρ ⇓ ρʳ -> Is ρʳ
--   evalˢᵘᵇ  idˢᵘᵇ⇓       = _
--   evalˢᵘᵇ  ↑⇓           = _
--   evalˢᵘᵇ (eψ ▻ˢᵘᵇ⇓ ex) = _▻ᵉⁿᵛ_ <$> evalˢᵘᵇ eψ <*> eval ex
--   evalˢᵘᵇ (eφ ∘ˢᵘᵇ⇓ eψ) = evalˢᵘᵇ eψ

mutual
  quoteⁿᶠ : ∀ {Γ σ} {xˢ : ⟦ Γ ⊢ⁿᶠ σ ⟧} {xʳ} -> Quoteⁿᶠ xˢ ⇓ xʳ -> Is xʳ
  quoteⁿᶠ {xˢ = neˢᵉᵐ _} (ne⇓ qx)    = neⁿᶠ <$> quoteⁿᵉ qx
  quoteⁿᶠ                (ƛ⇓_ ax qx) = ƛⁿᶠ_ <$> quoteⁿᶠ qx

  quoteⁿᵉ : ∀ {Γ σ} {xˢ : ⟦ Γ ⊢ⁿᵉ σ ⟧} {xʳ} -> Quoteⁿᵉ xˢ ⇓ xʳ -> Is xʳ
  quoteⁿᵉ {xˢ = var _}  var⇓      = _
  quoteⁿᵉ {xˢ = _ ∙ _} (qf ∙⇓ qx) = _∙_ <$> quoteⁿᵉ qf <*> quoteⁿᶠ qx

norm : ∀ {Γ σ} {x : Γ ⊢ σ} {xʳ : Γ ⊢ⁿᶠ σ} -> Norm x ⇓ xʳ -> Is xʳ
norm (norm⇓ _ qx) = quoteⁿᶠ qx

nf : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ⁿᶠ σ
nf = ¡ ∘ norm ∘ proj₂ ∘ ∃-Norm

stabilityᵛᵃʳ : ∀ {Γ} -> (v : ⋆ ∈ Γ) -> nf (embᵛᵃʳ v) ≡ neⁿᶠ (var v)
stabilityᵛᵃʳ  vz    = refl
stabilityᵛᵃʳ (vs v) = {!!}

mutual
  stabilityⁿᶠ : ∀ {Γ σ} -> (x : Γ ⊢ⁿᶠ σ) -> nf (embⁿᶠ x) ≡ x
  stabilityⁿᶠ (neⁿᶠ x) = stabilityⁿᵉ x
  stabilityⁿᶠ (ƛⁿᶠ  b) = {!!}

  stabilityⁿᵉ : ∀ {Γ} -> (x : Γ ⊢ⁿᵉ ⋆) -> nf (embⁿᵉ x) ≡ neⁿᶠ x
  stabilityⁿᵉ (var v) = stabilityᵛᵃʳ v
  stabilityⁿᵉ (f ∙ x) = {!!}
