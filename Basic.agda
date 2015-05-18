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
    _∘ˢᵘᵇ_ : ∀ {Γ Δ Θ} -> Δ ↦ Θ -> Γ ↦ Δ -> Γ ↦ Θ
    _▻ˢᵘᵇ_ : ∀ {Γ Δ σ} -> Γ ↦ Δ -> Δ ⊢ σ -> Γ ▻ σ ↦ Δ
    ↑      : ∀ {Γ σ}   -> Γ ↦ Γ ▻ σ

data _∈_ : Type -> Con -> Set where
  vz : ∀ {Γ σ}   -> σ ∈ Γ ▻ σ
  vs : ∀ {Γ σ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

data _⊢ⁿᵉ[_]_ Γ (B : Con -> Type -> Set) : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ            -> Γ ⊢ⁿᵉ[ B ] σ
  _∙_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ[ B ] σ ⇒ τ -> B Γ σ        -> Γ ⊢ⁿᵉ[ B ] τ

mutual
  data _⊢ⁿᶠ_ Γ : Type -> Set where
    neⁿᶠ : Γ ⊢ⁿᵉ ⋆ -> Γ ⊢ⁿᶠ ⋆
    ƛⁿᶠ  : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ

  _⊢ⁿᵉ_ : Con -> Type -> Set
  Γ ⊢ⁿᵉ σ = Γ ⊢ⁿᵉ[ _⊢ⁿᶠ_ ] σ

data Env (B : Con -> Type -> Set) Δ : Con -> Set where
  εᵉⁿᵛ   : Env B Δ ε
  _▻ᵉⁿᵛ_ : ∀ {Γ σ} -> Env B Δ Γ -> B Δ σ -> Env B Δ (Γ ▻ σ)

mutual
  data ⟦_⊢ⁿᶠ_⟧ Δ : Type -> Set where
    neˢᵉᵐ : ∀ {σ}     -> ⟦ Δ ⊢ⁿᵉ σ ⟧ -> ⟦ Δ ⊢ⁿᶠ σ ⟧
    ƛˢᵉᵐ  : ∀ {Γ σ τ} -> Γ ▻ σ ⊢ τ   -> ⟦ Γ ↦ Δ ⟧   -> ⟦ Δ ⊢ⁿᶠ σ ⇒ τ ⟧

  ⟦_⊢ⁿᵉ_⟧ : Con -> Type -> Set
  ⟦ Γ ⊢ⁿᵉ σ ⟧ = Γ ⊢ⁿᵉ[ ⟦_⊢ⁿᶠ_⟧ ] σ

  ⟦_↦_⟧ : Con -> Con -> Set
  ⟦ Γ ↦ Δ ⟧ = Env ⟦_⊢ⁿᶠ_⟧ Δ Γ

data _⊂_ : Con -> Con -> Set where
  stop : ∀ {Γ σ}   -> Γ ⊂ Γ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊂ Δ     -> Γ ▻ σ ⊂ Δ ▻ σ

embᵛᵃʳ : ∀ {Γ σ} -> σ ∈ Γ -> Γ ⊢ σ
embᵛᵃʳ  vz    = ø
embᵛᵃʳ (vs v) = embᵛᵃʳ v [ ↑ ]

ε↦Γ : ∀ {Γ} -> ε ↦ Γ
ε↦Γ {ε}     = idˢᵘᵇ
ε↦Γ {Γ ▻ σ} = ↑ ∘ˢᵘᵇ ε↦Γ

mutual
  embⁿᵉ : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ
  embⁿᵉ (var v) = embᵛᵃʳ v
  embⁿᵉ (f ∙ x) = embⁿᵉ f ∙ embⁿᶠ x

  embⁿᶠ : ∀ {Γ σ} -> Γ ⊢ⁿᶠ σ -> Γ ⊢ σ
  embⁿᶠ (neⁿᶠ n) = embⁿᵉ n
  embⁿᶠ (ƛⁿᶠ  b) = ƛ (embⁿᶠ b)

mutual
  emb⟦⟧ⁿᵉ : ∀ {Γ σ} -> ⟦ Γ ⊢ⁿᵉ σ ⟧ -> Γ ⊢ σ
  emb⟦⟧ⁿᵉ (var v) = embᵛᵃʳ v
  emb⟦⟧ⁿᵉ (f ∙ x) = emb⟦⟧ⁿᵉ f ∙ emb⟦⟧ⁿᶠ x

  emb⟦⟧ⁿᶠ : ∀ {Γ σ} -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> Γ ⊢ σ
  emb⟦⟧ⁿᶠ (neˢᵉᵐ  n) = emb⟦⟧ⁿᵉ n
  emb⟦⟧ⁿᶠ (ƛˢᵉᵐ b ρ) = (ƛ b) [ emb⟦⟧ᵉⁿᵛ ρ ]

  emb⟦⟧ᵉⁿᵛ : ∀ {Γ Δ} -> ⟦ Γ ↦ Δ ⟧ -> Γ ↦ Δ
  emb⟦⟧ᵉⁿᵛ  εᵉⁿᵛ       = ε↦Γ
  emb⟦⟧ᵉⁿᵛ (ρ ▻ᵉⁿᵛ xˢ) = emb⟦⟧ᵉⁿᵛ ρ ▻ˢᵘᵇ emb⟦⟧ⁿᶠ xˢ

wkᵛᵃʳ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> σ ∈ Γ -> σ ∈ Δ
wkᵛᵃʳ  stop       v     = vs v
wkᵛᵃʳ (keep sub)  vz    = vz
wkᵛᵃʳ (keep sub) (vs v) = vs (wkᵛᵃʳ sub v)

mutual
  wk⟦⟧ⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> ⟦ Γ ⊢ⁿᵉ σ ⟧ -> ⟦ Δ ⊢ⁿᵉ σ ⟧
  wk⟦⟧ⁿᵉ sub (var v) = var (wkᵛᵃʳ sub v)
  wk⟦⟧ⁿᵉ sub (f ∙ x) = wk⟦⟧ⁿᵉ sub f ∙ wk⟦⟧ⁿᶠ sub x

  wk⟦⟧ⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> ⟦ Δ ⊢ⁿᶠ σ ⟧
  wk⟦⟧ⁿᶠ sub (neˢᵉᵐ n)  = neˢᵉᵐ (wk⟦⟧ⁿᵉ sub n)
  wk⟦⟧ⁿᶠ sub (ƛˢᵉᵐ b ρ) = ƛˢᵉᵐ b (wk⟦⟧ᵉⁿᵛ sub ρ)

  wk⟦⟧ᵉⁿᵛ : ∀ {Γ Δ Θ} -> Δ ⊂ Θ -> ⟦ Γ ↦ Δ ⟧ -> ⟦ Γ ↦ Θ ⟧
  wk⟦⟧ᵉⁿᵛ sub  εᵉⁿᵛ       = εᵉⁿᵛ
  wk⟦⟧ᵉⁿᵛ sub (ρ ▻ᵉⁿᵛ xˢ) = wk⟦⟧ᵉⁿᵛ sub ρ ▻ᵉⁿᵛ wk⟦⟧ⁿᶠ sub xˢ

mutual
  wkⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  wkⁿᵉ sub (var v) = var (wkᵛᵃʳ sub v)
  wkⁿᵉ sub (f ∙ x) = wkⁿᵉ sub f ∙ wkⁿᶠ sub x

  wkⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊂ Δ -> Γ ⊢ⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  wkⁿᶠ sub (neⁿᶠ n) = neⁿᶠ (wkⁿᵉ sub n)
  wkⁿᶠ sub (ƛⁿᶠ  b) = ƛⁿᶠ (wkⁿᶠ (keep sub) b)

pop⟦⟧ⁿᶠ : ∀ {Γ σ τ} -> ⟦ Γ ⊢ⁿᶠ τ ⟧ -> ⟦ Γ ▻ σ ⊢ⁿᶠ τ ⟧
pop⟦⟧ⁿᶠ = wk⟦⟧ⁿᶠ stop

idᵉⁿᵛ : ∀ {Γ} -> ⟦ Γ ↦ Γ ⟧
idᵉⁿᵛ {ε}     = εᵉⁿᵛ
idᵉⁿᵛ {Γ ▻ σ} = (wk⟦⟧ᵉⁿᵛ stop idᵉⁿᵛ) ▻ᵉⁿᵛ neˢᵉᵐ (var vz)

_[_]⁰ : ∀ {Γ σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ -> Γ ⊢ τ
b [ x ]⁰ = b [ idˢᵘᵇ ▻ˢᵘᵇ x ]
