infix  1 _⊢_ _↦_ _∈_ _⊢ⁿᵉ[_]_ _⊢ⁿᶠ_ _⊢ⁿᵉ_ _⊂_
infixr 3 _⇒_
infixl 5 _▻_
infixr 3 ƛ_
infixl 5 _∙_
infixl 6 _[_]
infixr 6 _∘ˢᵘᵇ_
infixr 5 _▻ˢᵘᵇ_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

mutual
  data _⊢_ : Con -> Type -> Set where
    ø    : ∀ {Γ σ}   -> Γ ▻ σ ⊢ σ
    ƛ_   : ∀ {Γ σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
    _∙_  : ∀ {Γ σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
    _[_] : ∀ {Γ Δ σ} -> Γ ⊢ σ     -> Γ ↦ Δ     -> Δ ⊢ σ

  data _↦_ : Con -> Con -> Set where
    idˢᵘᵇ  : ∀ {Γ}     -> Γ ↦ Γ
    _∘ˢᵘᵇ_ : ∀ {Γ Δ Σ} -> Γ ↦ Δ -> Δ ↦ Σ -> Γ ↦ Σ
    _▻ˢᵘᵇ_ : ∀ {Γ Δ σ} -> Γ ↦ Δ -> Δ ⊢ σ -> Γ ▻ σ ↦ Δ
    ↑      : ∀ {Γ σ}   -> Γ ↦ Γ ▻ σ

data _∈_ : Type -> Con -> Set where
  vz : ∀ {Γ σ}   -> σ ∈ Γ ▻ σ
  vs : ∀ {Γ σ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

data _⊢ⁿᵉ[_]_ Γ (B : Con -> Type -> Set) : Type -> Set where
  varⁿ : ∀ {σ}   -> σ ∈ Γ            -> Γ ⊢ⁿᵉ[ B ] σ
  _∙ⁿ_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ[ B ] σ ⇒ τ -> B Γ σ        -> Γ ⊢ⁿᵉ[ B ] τ

data Env (B : Con -> Type -> Set) Δ : Con -> Set where
  εᵉⁿᵛ   : Env B Δ ε
  _▻ᵉⁿᵛ_ : ∀ {Γ σ} -> Env B Δ Γ -> B Δ σ -> Env B Δ (Γ ▻ σ)

mutual
  data ⟦_⊢ⁿᶠ_⟧ Δ : Type -> Set where
    neˢᵉᵐ : ∀ {σ}     -> ⟦ Δ ⊢ⁿᵉ σ ⟧ -> ⟦ Δ ⊢ⁿᶠ σ ⟧
    ƛˢᵉᵐ  : ∀ {Γ σ τ} -> Γ ▻ σ ⊢ τ   -> ⟦ Γ ↦ Δ ⟧   -> ⟦ Δ ⊢ⁿᶠ σ ⇒ τ ⟧

  ⟦_↦_⟧ : Con -> Con -> Set
  ⟦ Γ ↦ Δ ⟧ = Env ⟦_⊢ⁿᶠ_⟧ Δ Γ

  ⟦_⊢ⁿᵉ_⟧ : Con -> Type -> Set
  ⟦ Γ ⊢ⁿᵉ σ ⟧ = Γ ⊢ⁿᵉ[ ⟦_⊢ⁿᶠ_⟧ ] σ

mutual
  data _⊢ⁿᶠ_ Γ : Type -> Set where
    neⁿ : Γ ⊢ⁿᵉ ⋆ -> Γ ⊢ⁿᶠ ⋆
    ƛⁿ  : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ

  _⊢ⁿᵉ_ : Con -> Type -> Set
  Γ ⊢ⁿᵉ σ = Γ ⊢ⁿᵉ[ _⊢ⁿᶠ_ ] σ

data _⊂_ : Con -> Con -> Set where
  stop : ∀ {Γ σ}   -> Γ ⊂ Γ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊂ Δ     -> Γ ▻ σ ⊂ Δ ▻ σ

embᵛᵃʳ : ∀ {Γ σ} -> σ ∈ Γ -> Γ ⊢ σ
embᵛᵃʳ  vz    = ø
embᵛᵃʳ (vs v) = embᵛᵃʳ v [ ↑ ]

ε↦Γ : ∀ {Γ} -> ε ↦ Γ
ε↦Γ {ε}     = idˢᵘᵇ
ε↦Γ {Γ ▻ σ} = ε↦Γ ∘ˢᵘᵇ ↑

mutual
  embⁿᵉ : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ
  embⁿᵉ (varⁿ v) = embᵛᵃʳ v
  embⁿᵉ (f ∙ⁿ x) = embⁿᵉ f ∙ embⁿᶠ x

  embⁿᶠ : ∀ {Γ σ} -> Γ ⊢ⁿᶠ σ -> Γ ⊢ σ
  embⁿᶠ (neⁿ n) = embⁿᵉ n
  embⁿᶠ (ƛⁿ b)  = ƛ (embⁿᶠ b)

mutual
  emb⟦⟧ⁿᵉ : ∀ {Γ σ} -> ⟦ Γ ⊢ⁿᵉ σ ⟧ -> Γ ⊢ σ
  emb⟦⟧ⁿᵉ (varⁿ v) = embᵛᵃʳ v
  emb⟦⟧ⁿᵉ (f ∙ⁿ x) = emb⟦⟧ⁿᵉ f ∙ emb⟦⟧ⁿᶠ x

  emb⟦⟧ⁿᶠ : ∀ {Γ σ} -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> Γ ⊢ σ
  emb⟦⟧ⁿᶠ (neˢᵉᵐ n)  = emb⟦⟧ⁿᵉ n
  emb⟦⟧ⁿᶠ (ƛˢᵉᵐ b ρ) = (ƛ b) [ emb⟦⟧ᵉⁿᵛ ρ ]

  emb⟦⟧ᵉⁿᵛ : ∀ {Γ Δ} -> ⟦ Γ ↦ Δ ⟧ -> Γ ↦ Δ
  emb⟦⟧ᵉⁿᵛ  εᵉⁿᵛ      = ε↦Γ
  emb⟦⟧ᵉⁿᵛ (ρ ▻ᵉⁿᵛ s) = emb⟦⟧ᵉⁿᵛ ρ ▻ˢᵘᵇ emb⟦⟧ⁿᶠ s

wkᵛᵃʳ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> σ ∈ Γ -> σ ∈ Δ
wkᵛᵃʳ  stop       v     = vs v
wkᵛᵃʳ (keep sub)  vz    = vz
wkᵛᵃʳ (keep sub) (vs v) = vs (wkᵛᵃʳ sub v)

mutual
  wk⟦⟧ⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> ⟦ Γ ⊢ⁿᵉ σ ⟧ -> ⟦ Δ ⊢ⁿᵉ σ ⟧
  wk⟦⟧ⁿᵉ sub (varⁿ v) = varⁿ (wkᵛᵃʳ sub v)
  wk⟦⟧ⁿᵉ sub (f ∙ⁿ x) = wk⟦⟧ⁿᵉ sub f ∙ⁿ wk⟦⟧ⁿᶠ sub x

  wk⟦⟧ⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> ⟦ Δ ⊢ⁿᶠ σ ⟧
  wk⟦⟧ⁿᶠ sub (neˢᵉᵐ n)  = neˢᵉᵐ (wk⟦⟧ⁿᵉ sub n)
  wk⟦⟧ⁿᶠ sub (ƛˢᵉᵐ b ρ) = ƛˢᵉᵐ b (wk⟦⟧ᵉⁿᵛ sub ρ)

  wk⟦⟧ᵉⁿᵛ : ∀ {Γ Δ Σ} -> Δ ⊂ Σ -> ⟦ Γ ↦ Δ ⟧ -> ⟦ Γ ↦ Σ ⟧
  wk⟦⟧ᵉⁿᵛ sub  εᵉⁿᵛ      = εᵉⁿᵛ
  wk⟦⟧ᵉⁿᵛ sub (ρ ▻ᵉⁿᵛ s) = wk⟦⟧ᵉⁿᵛ sub ρ ▻ᵉⁿᵛ wk⟦⟧ⁿᶠ sub s

mutual
  wkⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  wkⁿᵉ sub (varⁿ v) = varⁿ (wkᵛᵃʳ sub v)
  wkⁿᵉ sub (f ∙ⁿ x) = wkⁿᵉ sub f ∙ⁿ wkⁿᶠ sub x

  wkⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> Γ ⊢ⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  wkⁿᶠ sub (neⁿ n) = neⁿ (wkⁿᵉ sub n)
  wkⁿᶠ sub (ƛⁿ  b) = ƛⁿ (wkⁿᶠ (keep sub) b)

_[_]⁰ : ∀ {Γ σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ -> Γ ⊢ τ
b [ x ]⁰ = b [ idˢᵘᵇ ▻ˢᵘᵇ x ]

idᵉⁿᵛ : ∀ {Γ} -> ⟦ Γ ↦ Γ ⟧
idᵉⁿᵛ {ε}     = εᵉⁿᵛ
idᵉⁿᵛ {Γ ▻ σ} = (wk⟦⟧ᵉⁿᵛ stop idᵉⁿᵛ) ▻ᵉⁿᵛ neˢᵉᵐ (varⁿ vz)
