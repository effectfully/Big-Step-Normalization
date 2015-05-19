open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Basic
open import BigStep
open import Properties
open import SCV
open import Lemmas

∃-Norm : ∀ {Γ σ} -> (x : Γ ⊢ σ) -> ∃ λ xʳ -> Norm x ⇓ xʳ 
∃-Norm x =
  case ⟦ x ⟧& idˢᶜᵉ of λ{
    (xˢʳ , ex , xˢᶜᵛ) -> case quoteˢᶜᵛ xˢᶜᵛ of λ{
      (xʳ , qx) -> xʳ , norm⇓ ex qx
    }
  }

nf : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ⁿᶠ σ
nf = proj₁ ∘ ∃-Norm
