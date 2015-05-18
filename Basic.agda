infix  1 _⊢_ _↦_ _∈_ _⊢ⁿᵉ[_]_ _⊢ⁿᶠ_ _⊢ⁿᵉ_ _⊆_
infixr 3 _⇒_
infixl 5 _▻_
infixr 3 ƛ_
infixl 5 _∙_
infixl 6 _[_]
infixr 6 _∘ˢᵘᵇ_
infixr 5 _▻ˢᵘᵇ_
infixr 8 _∘ᵒᵖᵉ_

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
    ↑      : ∀ {Γ σ}   -> Γ ↦ Γ ▻ σ
    _▻ˢᵘᵇ_ : ∀ {Γ Δ σ} -> Γ ↦ Δ -> Δ ⊢ σ -> Γ ▻ σ ↦ Δ
    _∘ˢᵘᵇ_ : ∀ {Γ Δ Θ} -> Δ ↦ Θ -> Γ ↦ Δ -> Γ ↦ Θ

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
  
data _⊆_ : Con -> Con -> Set where
  stop : ε ⊆ ε
  skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

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
  emb⟦⟧ⁿᵉ (var v)   = embᵛᵃʳ v
  emb⟦⟧ⁿᵉ (fˢ ∙ xˢ) = emb⟦⟧ⁿᵉ fˢ ∙ emb⟦⟧ⁿᶠ xˢ

  emb⟦⟧ⁿᶠ : ∀ {Γ σ} -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> Γ ⊢ σ
  emb⟦⟧ⁿᶠ (neˢᵉᵐ  xˢ) = emb⟦⟧ⁿᵉ xˢ
  emb⟦⟧ⁿᶠ (ƛˢᵉᵐ bˢ ρ) = (ƛ bˢ) [ emb⟦⟧ᵉⁿᵛ ρ ]

  emb⟦⟧ᵉⁿᵛ : ∀ {Γ Δ} -> ⟦ Γ ↦ Δ ⟧ -> Γ ↦ Δ
  emb⟦⟧ᵉⁿᵛ  εᵉⁿᵛ       = ε↦Γ
  emb⟦⟧ᵉⁿᵛ (ρ ▻ᵉⁿᵛ xˢ) = emb⟦⟧ᵉⁿᵛ ρ ▻ˢᵘᵇ emb⟦⟧ⁿᶠ xˢ

wkᵛᵃʳ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
wkᵛᵃʳ  stop     ()
wkᵛᵃʳ (skip ι)  v     = vs (wkᵛᵃʳ ι v)
wkᵛᵃʳ (keep ι)  vz    = vz
wkᵛᵃʳ (keep ι) (vs v) = vs (wkᵛᵃʳ ι v)

mutual
  wkⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  wkⁿᵉ ι (var v) = var (wkᵛᵃʳ ι v)
  wkⁿᵉ ι (f ∙ x) = wkⁿᵉ ι f ∙ wkⁿᶠ ι x

  wkⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  wkⁿᶠ ι (neⁿᶠ n) = neⁿᶠ (wkⁿᵉ ι n)
  wkⁿᶠ ι (ƛⁿᶠ  b) = ƛⁿᶠ (wkⁿᶠ (keep ι) b)

mutual
  wk⟦⟧ⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> ⟦ Γ ⊢ⁿᵉ σ ⟧ -> ⟦ Δ ⊢ⁿᵉ σ ⟧
  wk⟦⟧ⁿᵉ ι (var v)   = var (wkᵛᵃʳ ι v)
  wk⟦⟧ⁿᵉ ι (fˢ ∙ xˢ) = wk⟦⟧ⁿᵉ ι fˢ ∙ wk⟦⟧ⁿᶠ ι xˢ

  wk⟦⟧ⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> ⟦ Γ ⊢ⁿᶠ σ ⟧ -> ⟦ Δ ⊢ⁿᶠ σ ⟧
  wk⟦⟧ⁿᶠ ι (neˢᵉᵐ xˢ)  = neˢᵉᵐ (wk⟦⟧ⁿᵉ ι xˢ)
  wk⟦⟧ⁿᶠ ι (ƛˢᵉᵐ bˢ ρ) = ƛˢᵉᵐ bˢ (wk⟦⟧ᵉⁿᵛ ι ρ)

  wk⟦⟧ᵉⁿᵛ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> ⟦ Γ ↦ Δ ⟧ -> ⟦ Γ ↦ Θ ⟧
  wk⟦⟧ᵉⁿᵛ ι  εᵉⁿᵛ       = εᵉⁿᵛ
  wk⟦⟧ᵉⁿᵛ ι (ρ ▻ᵉⁿᵛ xˢ) = wk⟦⟧ᵉⁿᵛ ι ρ ▻ᵉⁿᵛ wk⟦⟧ⁿᶠ ι xˢ

idᵒᵖᵉ : ∀ {Γ} -> Γ ⊆ Γ
idᵒᵖᵉ {ε}     = stop
idᵒᵖᵉ {Γ ▻ σ} = keep idᵒᵖᵉ

topᵒᵖᵉ : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
topᵒᵖᵉ = skip idᵒᵖᵉ

_∘ᵒᵖᵉ_ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
stop   ∘ᵒᵖᵉ stop   = stop
skip ι ∘ᵒᵖᵉ κ      = skip (ι ∘ᵒᵖᵉ κ)
keep ι ∘ᵒᵖᵉ skip κ = skip (ι ∘ᵒᵖᵉ κ)
keep ι ∘ᵒᵖᵉ keep κ = keep (ι ∘ᵒᵖᵉ κ)

pop⟦⟧ⁿᶠ : ∀ {Γ σ τ} -> ⟦ Γ ⊢ⁿᶠ τ ⟧ -> ⟦ Γ ▻ σ ⊢ⁿᶠ τ ⟧
pop⟦⟧ⁿᶠ = wk⟦⟧ⁿᶠ topᵒᵖᵉ

varˢᵉᵐ : ∀ {Γ σ} -> σ ∈ Γ -> ⟦ Γ ⊢ⁿᶠ σ ⟧
varˢᵉᵐ v = neˢᵉᵐ (var v)

idᵉⁿᵛ : ∀ {Γ} -> ⟦ Γ ↦ Γ ⟧
idᵉⁿᵛ {ε}     = εᵉⁿᵛ
idᵉⁿᵛ {Γ ▻ σ} = (wk⟦⟧ᵉⁿᵛ topᵒᵖᵉ idᵉⁿᵛ) ▻ᵉⁿᵛ varˢᵉᵐ vz

_[_]⁰ : ∀ {Γ σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ -> Γ ⊢ τ
e [ x ]⁰ = e [ idˢᵘᵇ ▻ˢᵘᵇ x ]
