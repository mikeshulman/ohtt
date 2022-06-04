{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

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

infixl 30 _▸_ _►_ _∷_

postulate
  βtop : {Δ : Tel} {B : el Δ → Type} (a : el Δ) (b : B a) → top {B = B} (a ∷ b) ≡ b

{-# REWRITE βtop #-}

uncurry : {T : Type} {Δ : Tel} {A : el Δ → Type} (B : (w : el Δ) → A w → T) → el (Δ ▸ A) → T
uncurry B w = B (pop w) (top w)

eq-coe← : {Δ : Tel} {B : el Δ → Type} {a₀ a₁ : el Δ} (a₂ : a₀ ≡ a₁) {b₁ : B a₁} →
  (a₀ ∷ coe← (cong B a₂) b₁) ≡ (a₁ ∷ b₁)
eq-coe← reflᵉ = reflᵉ

----------------------------------------
-- Concatenation of telescopes
----------------------------------------

-- Concatenation of telescopes is defined by recursion on the second
-- argument.  Morally, the definition should look like this:

{-
_►_ : (Δ : Tel) (Θ : el Δ → Tel) → Tel
Δ ► (λ _ → ε) = Δ
Δ ► (λ w → Θ w ▸ A w) = (Δ ► Θ) ▸ "A"
-}

-- However, this doesn't actually make sense because it's trying to
-- pattern-match under a λ.  Thus, we instead postulate concatenation
-- and give its definition with rewrite rules.  In addition, in order
-- to make sense of the "A" above we need to treat ► as a kind of
-- Σ-type on elements, with its own pairing and projection functions.
postulate
  _►_ : (Δ : Tel) (Θ : el Δ → Tel) → Tel
  POP : {Δ : Tel} (Θ : el Δ → Tel) → el (Δ ► Θ) → el Δ
  TOP : {Δ : Tel} (Θ : el Δ → Tel) (w : el (Δ ► Θ)) → el (Θ (POP Θ w))
  PAIR : {Δ : Tel} (Θ : el Δ → Tel) (w : el Δ) → el (Θ w) → el (Δ ► Θ)
  βPOP : {Δ : Tel} {Θ : el Δ → Tel} (w : el Δ) (v : el (Θ w)) → POP Θ (PAIR Θ w v) ≡ w
  ηPAIR : {Δ : Tel} {Θ : el Δ → Tel} (w : el (Δ ► Θ)) → (PAIR Θ (POP Θ w) (TOP Θ w)) ≡ w
  ►ε : (Δ : Tel) → Δ ► (λ _ → ε) ≡ Δ
  ►▸ : (Δ : Tel) (Θ : el Δ → Tel) (A : (w : el Δ) → el (Θ w) → Type) →
    Δ ► (λ w → Θ w ▸ A w) ≡ (Δ ► Θ) ▸ (λ w → A (POP Θ w) (TOP Θ w))

{-# REWRITE βPOP ηPAIR ►ε ►▸ #-}

postulate
  βTOP : {Δ : Tel} {Θ : el Δ → Tel} (w : el Δ) (v : el (Θ w)) → TOP Θ (PAIR Θ w v) ≡ v

{-# REWRITE βTOP #-}

-- We also make these consistent, by giving rules for POP, TOP, and
-- PAIR on the cases for the right-hand argument.
postulate
  POPε : (Δ : Tel) (w : el Δ) → POP (λ _ → ε) w ≡ w
  TOPε : (Δ : Tel) (w : el Δ) → TOP (λ _ → ε) w ≡ []
  PAIRε : (Δ : Tel) (w : el Δ) (v : el ε) → (PAIR (λ _ → ε) w v) ≡ w
  POP▸ : (Δ : Tel) (Θ : el Δ → Tel) (A : (w : el Δ) → el (Θ w) → Type)
    (w : el (Δ ► (λ v → Θ v ▸ A v))) → POP (λ v → Θ v ▸ A v) w ≡ POP Θ (pop w)

{-# REWRITE POPε TOPε PAIRε POP▸ #-}

postulate
  TOP▸ : (Δ : Tel) (Θ : el Δ → Tel) (A : (w : el Δ) → el (Θ w) → Type)
    (w : el (Δ ► (λ v → Θ v ▸ A v))) → TOP (λ v → Θ v ▸ A v) w ≡ (TOP Θ (pop w) ∷ top w)

{-# REWRITE TOP▸ #-}

postulate
  PAIR▸ : (Δ : Tel) (Θ : el Δ → Tel) (A : (w : el Δ) → el (Θ w) → Type) (w : el Δ) (v : el (Θ w ▸ A w)) →
    (PAIR (λ w → Θ w ▸ A w) w v) ≡ (PAIR Θ w (pop v)) ∷ top v

{-# REWRITE PAIR▸ #-}

UNCURRY : {T : Typeᵉ} {Δ : Tel} (Θ : el Δ → Tel) (Γ : (w : el Δ) → el (Θ w) → T) → el (Δ ► Θ) → T
UNCURRY Θ B w = B (POP Θ w) (TOP Θ w)

-- Special names for the non-dependent case

PROD : Tel → Tel → Tel
PROD Δ Θ = Δ ► (λ _ → Θ)

FST : (Δ Θ : Tel) → el (PROD Δ Θ) → el Δ
FST Δ Θ w = POP (λ _ → Θ) w

SND : (Δ Θ : Tel) → el (PROD Δ Θ) → el Θ
SND Δ Θ w = TOP (λ _ → Θ) w

PR : (Δ Θ : Tel) → el Δ → el Θ → el (PROD Δ Θ)
PR Δ Θ u v = PAIR (λ _ → Θ) u v

------------------------------
-- Equality of telescopes
------------------------------

COE→ : {Γ Δ : Tel} (e : Γ ≡ Δ) → el Γ → el Δ
COE→ e x = coe→ᵉ (cong el e) x

COE← : {Γ Δ : Tel} (e : Γ ≡ Δ) → el Δ → el Γ
COE← e x = coe←ᵉ (cong el e) x

COE→COE→ : {Γ Δ Θ : Tel} (p : Γ ≡ Δ) (q : Δ ≡ Θ) (r : Γ ≡ Θ) {x : el Γ} → COE→ q (COE→ p x) ≡ COE→ r x
COE→COE→ p q r = coe→coe→ᵉ (cong el p) (cong el q) (cong el r)

COE←COE← : {Γ Δ Θ : Tel} (p : Γ ≡ Δ) (q : Δ ≡ Θ) (r : Γ ≡ Θ) {x : el Θ} → COE← p (COE← q x) ≡ COE← r x
COE←COE← p q r = coe←coe←ᵉ (cong el p) (cong el q) (cong el r)

_▸≡_ : {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → Type} {A₁ : el Δ₁ → Type} (e : Δ₀ ≡ Δ₁) (f : A₀ ≡[ e ] A₁) → (Δ₀ ▸ A₀) ≡ (Δ₁ ▸ A₁)
_▸≡_ reflᵉ reflᵉ = reflᵉ

_►≡_ : {Δ₀ Δ₁ : Tel} {Θ₀ : el Δ₀ → Tel} {Θ₁ : el Δ₁ → Tel} (e : Δ₀ ≡ Δ₁) (f : Θ₀ ≡[ e ] Θ₁) → (Δ₀ ► Θ₀) ≡ (Δ₁ ► Θ₁)
_►≡_ reflᵉ reflᵉ = reflᵉ

postulate
  ≡λ : {T : Typeᵉ} {Δ₀ Δ₁ : Tel} {A₀ : el Δ₀ → T} {A₁ : el Δ₁ → T} {e : Δ₀ ≡ Δ₁} →
    ((x₀ : el Δ₀) (x₁ : el Δ₁) (x₂ : x₀ ≡[ e ] x₁) → A₀ x₀ ≡ A₁ x₁) → A₀ ≡[ e ] A₁
  ≡λreflᵉ : {T : Typeᵉ} {Δ : Tel} (A : el Δ → T) (f : (x₀ : el Δ) (x₁ : el Δ) (x₂ : x₀ ≡ x₁) → A x₀ ≡ A x₁) →
    ≡λ {T} {Δ} {Δ} {A} {A} {reflᵉ} (λ x₀ x₁ x₂ → f x₀ x₁ x₂) ≡ reflᵉ

{-# REWRITE ≡λreflᵉ #-}
