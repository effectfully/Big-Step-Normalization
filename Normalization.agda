open import Function hiding (_$_)
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Basic
open import BigStep
open import Properties
open import SCV
open import Lemmas

nf : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ⁿᶠ σ
nf = proj₁ ∘ ∃-Norm

postulate
  unique : ∀ {Γ σ} {x : Γ ⊢ σ} {xʳ xʳ' : Γ ⊢ⁿᶠ σ}
         -> Norm x ⇓ xʳ -> Norm x ⇓ xʳ' -> xʳ ≡ xʳ'
  Embⁿᶠ : ∀ {Γ σ} -> (x : Γ ⊢ⁿᶠ σ) -> Norm embⁿᶠ x ⇓ x

stability : ∀ {Γ σ} -> (x : Γ ⊢ⁿᶠ σ) -> nf (embⁿᶠ x) ≡ x
stability x = unique (proj₁ (proj₂ (∃-Norm (embⁿᶠ x)))) (Embⁿᶠ x)
