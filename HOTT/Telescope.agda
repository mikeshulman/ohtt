{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Telescope where

open import HOTT.Rewrite

------------------------------
-- Telescope exo-types
------------------------------

-- We name the element of the terminal exotype [] because we think of
-- it as an empty list (the element of the empty telescope).
record ⊤ᵉ : Typeᵉ where
  constructor []

open ⊤ᵉ

-- A telescope is a list of dependent types.

data Tel : Typeᵉ

-- The elements of a telescope are defined by mutual
-- induction-recursion with the type Tel.
el : Tel → Typeᵉ

-- The definition of el involves a sort of Σ-exotype.  But rather than
-- make this a generic Σ-exotype, we make its first argument a Tel,
-- with the second argument depending on the first via el.  The reason
-- for this is explained below in the comments to ap-top.  Thus, it
-- also has to be defined mutually with Tel and el.  We make it a
-- postulate rather than an actual datatype because rewriting works
-- better that way.
postulate
  Σᵉ : (Δ : Tel) (B : el Δ → Type) → Typeᵉ

data Tel where
  ε : Tel
  _▸_ : (Δ : Tel) (A : el Δ → Type) → Tel

el ε = ⊤ᵉ
el (Δ ▸ A) = Σᵉ Δ A

-- Now we can give the constructors, destructors, and beta and eta
-- rules for Σᵉ.  We name the constructor ∷ because we think of the
-- elements of a telescope as a snoc-list, and we name its projections
-- 'top' and 'pop' because we think of them as De Bruijn Levels
-- accessing elements of such a list.
postulate
  _∷_ : {Δ : Tel} {B : el Δ → Type} (a : el Δ) (b : B a) → Σᵉ Δ B
  pop : {Δ : Tel} {B : el Δ → Type} (u : Σᵉ Δ B) → el Δ
  top : {Δ : Tel} {B : el Δ → Type} (u : Σᵉ Δ B) → B (pop u)
  βpop : {Δ : Tel} {B : el Δ → Type} (a : el Δ) (b : B a) → pop {B = B} (a ∷ b) ≡ a
  η∷ : {Δ : Tel} {B : el Δ → Type} (u : Σᵉ Δ B) → (pop u ∷ top u) ≡ u

{-# REWRITE βpop η∷ #-}

infixl 30 _▸_ _∷_

postulate
  βtop : {Δ : Tel} {B : el Δ → Type} (a : el Δ) (b : B a) → top {B = B} (a ∷ b) ≡ b

{-# REWRITE βtop #-}

uncurry : {T : Type} {Δ : Tel} {A : el Δ → Type} (B : (w : el Δ) → A w → T) → el (Δ ▸ A) → T
uncurry B w = B (pop w) (top w)

eq-coe← : {Δ : Tel} {B : el Δ → Type} {a₀ a₁ : el Δ} (a₂ : a₀ ≡ a₁) {b₁ : B a₁} →
  (a₀ ∷ coe← (cong B a₂) b₁) ≡ (a₁ ∷ b₁)
eq-coe← reflᵉ = reflᵉ

------------------------------
-- Equality of telescopes
------------------------------

COE→ : {Γ Δ : Tel} (e : Γ ≡ Δ) → el Γ → el Δ
COE→ e x = coe→ᵉ (cong el e) x

COE← : {Γ Δ : Tel} (e : Γ ≡ Δ) → el Δ → el Γ
COE← e x = coe←ᵉ (cong el e) x

COE→COE→ : {Γ Δ Θ : Tel} (p : Γ ≡ Δ) (q : Δ ≡ Θ) (r : Γ ≡ Θ) {x : el Γ} → COE→ q (COE→ p x) ≡ COE→ r x
COE→COE→ {Γ} {Δ} {Θ} p q r {x} = coe→coe→ᵉ {el Γ} {el Δ} {el Θ} (cong el p) (cong el q) (cong el r) {x}

COE←COE← : {Γ Δ Θ : Tel} (p : Γ ≡ Δ) (q : Δ ≡ Θ) (r : Γ ≡ Θ) {x : el Θ} → COE← p (COE← q x) ≡ COE← r x
COE←COE← {Γ} {Δ} {Θ}  p q r {x} = coe←coe←ᵉ {el Γ} {el Δ} {el Θ} (cong el p) (cong el q) (cong el r) {x}

_▸≡_ : {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → Type} {A₁ : el Δ₁ → Type} (e : Δ₀ ≡ Δ₁) (f : A₀ ≡[ e ] A₁) → (Δ₀ ▸ A₀) ≡ (Δ₁ ▸ A₁)
_▸≡_ reflᵉ reflᵉ = reflᵉ

∷≡ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (e : δ₀ ≡ δ₁) {a₀ : A δ₀} {a₁ : A δ₁} (f : a₀ ≡[ e ] a₁) →
  (δ₀ ∷ a₀) ≡ (δ₁ ∷ a₁)
∷≡ A reflᵉ reflᵉ = reflᵉ

∷≡ʰ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (e : δ₀ ≡ δ₁) {a₀ : A δ₀} {a₁ : A δ₁} (f : a₀ ≡ʰ a₁) →
  (δ₀ ∷ a₀) ≡ (δ₁ ∷ a₁)
∷≡ʰ A reflᵉ reflʰ = reflᵉ

postulate
  ▸≡-reflish : {Δ : Tel} (A : el Δ → Type) (e : Δ ≡ Δ) (f : A ≡[ e ] A) → (e ▸≡ f) ≡ reflᵉ

{-# REWRITE ▸≡-reflish #-}

postulate
  ≡λ : {T : Typeᵉ} {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → T} {A₁ : el Δ₁ → T} {e : Δ₀ ≡ Δ₁} →
    ((x₀ : el Δ₀) (x₁ : el Δ₁) (x₂ : x₀ ≡[ e ] x₁) → A₀ x₀ ≡ A₁ x₁) → A₀ ≡[ e ] A₁
  ≡λreflᵉ : {T : Typeᵉ} {Δ : Tel} (A : el Δ → T) (f : (x₀ : el Δ) (x₁ : el Δ) (x₂ : x₀ ≡ x₁) → A x₀ ≡ A x₁) →
    ≡λ {T} {Δ} {Δ} {A} {A} {reflᵉ} (λ x₀ x₁ x₂ → f x₀ x₁ x₂) ≡ reflᵉ

{-# REWRITE ≡λreflᵉ #-}

postulate
  ≡λ′→ : {T : Typeᵉ} {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → T} {A₁ : el Δ₁ → T} {e : Δ₀ ≡ Δ₁} →
    ((x₀ : el Δ₀) → A₀ x₀ ≡ A₁ (COE→ e x₀)) → A₀ ≡[ e ] A₁
  ≡λ′← : {T : Typeᵉ} {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → T} {A₁ : el Δ₁ → T} {e : Δ₀ ≡ Δ₁} →
    ((x₁ : el Δ₁) → A₀ (COE← e x₁) ≡ A₁ x₁) → A₀ ≡[ e ] A₁
  ≡λ′→reflᵉ : {T : Typeᵉ} {Δ : Tel} {A : el Δ → T} →
    ≡λ′→ {T} {Δ} {Δ} {A} {A} {reflᵉ} (λ x₀ → reflᵉ) ≡ reflᵉ
  ≡λ′←reflᵉ : {T : Typeᵉ} {Δ : Tel} {A : el Δ → T} →
    ≡λ′← {T} {Δ} {Δ} {A} {A} {reflᵉ} (λ x₁ → reflᵉ) ≡ reflᵉ

{-# REWRITE ≡λ′→reflᵉ ≡λ′←reflᵉ #-}

coe→[] : {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → Type} {A₁ : el Δ₁ → Type} (e : Δ₀ ≡ Δ₁) (f : A₀ ≡[ e ] A₁)
  {δ₀ : el Δ₀} (a₀ : A₀ δ₀) → A₁ (COE→ e δ₀)
coe→[] reflᵉ reflᵉ a₀ = a₀

coe←[] : {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → Type} {A₁ : el Δ₁ → Type} (e : Δ₀ ≡ Δ₁) (f : A₀ ≡[ e ] A₁)
  {δ₁ : el Δ₁} (a₁ : A₁ δ₁) → A₀ (COE← e δ₁)
coe←[] reflᵉ reflᵉ a₁ = a₁

COE→[] : {Δ₀ Δ₁ : Tel} {Θ₀ : el Δ₀ → Tel} {Θ₁ : el Δ₁ → Tel} (e : Δ₀ ≡ Δ₁) (f : Θ₀ ≡[ e ] Θ₁)
  {δ₀ : el Δ₀} (t₀ : el (Θ₀ δ₀)) → el (Θ₁ (COE→ e δ₀))
COE→[] reflᵉ reflᵉ t₀ = t₀

COE←[] : {Δ₀ Δ₁ : Tel} {Θ₀ : el Δ₀ → Tel} {Θ₁ : el Δ₁ → Tel} (e : Δ₀ ≡ Δ₁) (f : Θ₀ ≡[ e ] Θ₁)
  {δ₁ : el Δ₁} (t₁ : el (Θ₁ δ₁)) → el (Θ₀ (COE← e δ₁))
COE←[] reflᵉ reflᵉ t₁ = t₁

coe→[]≡ʰ : {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → Type} {A₁ : el Δ₁ → Type} (e : Δ₀ ≡ Δ₁) (f : A₀ ≡[ e ] A₁)
  {δ₀ : el Δ₀} (a₀ : A₀ δ₀) → coe→[] e f a₀ ≡ʰ a₀
coe→[]≡ʰ reflᵉ reflᵉ _ = reflʰ

coe←[]≡ʰ : {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → Type} {A₁ : el Δ₁ → Type} (e : Δ₀ ≡ Δ₁) (f : A₀ ≡[ e ] A₁)
  {δ₁ : el Δ₁} (a₁ : A₁ δ₁) → coe←[] e f a₁ ≡ʰ a₁
coe←[]≡ʰ reflᵉ reflᵉ _ = reflʰ

COE→[]≡ʰ : {Δ₀ Δ₁ : Tel} {Θ₀ : el Δ₀ → Tel} {Θ₁ : el Δ₁ → Tel} (e : Δ₀ ≡ Δ₁) (f : Θ₀ ≡[ e ] Θ₁)
  {δ₀ : el Δ₀} (t₀ : el (Θ₀ δ₀)) → COE→[] e f t₀ ≡ʰ t₀
COE→[]≡ʰ reflᵉ reflᵉ _ = reflʰ

COE←[]≡ʰ : {Δ₀ Δ₁ : Tel} {Θ₀ : el Δ₀ → Tel} {Θ₁ : el Δ₁ → Tel} (e : Δ₀ ≡ Δ₁) (f : Θ₀ ≡[ e ] Θ₁)
  {δ₁ : el Δ₁} (t₁ : el (Θ₁ δ₁)) → COE←[] e f t₁ ≡ʰ t₁
COE←[]≡ʰ reflᵉ reflᵉ _ = reflʰ

postulate
  COE→-▸≡ : {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → Type} {A₁ : el Δ₁ → Type} (e : Δ₀ ≡ Δ₁) (f : A₀ ≡[ e ] A₁) (δ₀ : el Δ₀) (a₀ : A₀ δ₀) →
    coe→ᵉ (cong el (e ▸≡ f)) (δ₀ ∷ a₀) ≡ (COE→ e δ₀ ∷ coe→[] e f a₀)
  COE←-▸≡ : {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → Type} {A₁ : el Δ₁ → Type} (e : Δ₀ ≡ Δ₁) (f : A₀ ≡[ e ] A₁) (δ₁ : el Δ₁) (a₁ : A₁ δ₁) →
    coe←ᵉ (cong el (e ▸≡ f)) (δ₁ ∷ a₁) ≡ (COE← e δ₁ ∷ coe←[] e f a₁)
    
{-# REWRITE COE→-▸≡ COE←-▸≡ #-}

postulate
  coe→[]-reflᵉ : {Δ : Tel} {A₀ A₁ : el Δ → Type} (f : (x₀ : el Δ) → A₀ x₀ ≡ A₁ x₀) {δ₀ : el Δ} (a₀ : A₀ δ₀) →
    coe→[] reflᵉ (≡λ′→ f) a₀ ≡ coe→ (f δ₀) a₀
  coe←[]-reflᵉ : {Δ : Tel} {A₀ A₁ : el Δ → Type} (f : (x₀ : el Δ) → A₀ x₀ ≡ A₁ x₀) {δ₁ : el Δ} (a₁ : A₁ δ₁) →
    coe←[] reflᵉ (≡λ′→ f) a₁ ≡ coe← (f δ₁) a₁

{-# REWRITE coe→[]-reflᵉ coe←[]-reflᵉ #-}
