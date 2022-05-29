{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Telescope where

open import HOTT.Rewrite

------------------------------
-- Telescope exo-types
------------------------------

record ⊤ᵉ : Typeᵉ where
  constructor []

open ⊤ᵉ

-- A telescope is a list of dependent types.  From it we can extract
-- an exotype of elements, using either kind of exo-sigma.

data Tel : Typeᵉ

-- The elements of a telescope are defined by mutual
-- induction-recursion with the type Tel.
el : Tel → Typeᵉ

-- Its definition, in turn, involves a sort of Σ-exotype.  But rather
-- than make this a generic Σ-exotype, we make its first argument a
-- Tel, with the second argument depending on the first via el.  The
-- reason for this is explained below in the comments to ap-top.
-- Thus, it also has to be postulated mutually with Tel and el.
postulate
  Σᵉ : (Δ : Tel) (B : el Δ → Type) → Typeᵉ

data Tel where
  ε : Tel
  _▸_ : (Δ : Tel) (A : el Δ → Type) → Tel

el ε = ⊤ᵉ
el (Δ ▸ A) = Σᵉ Δ A

-- Now we can give the constructors, destructors, and beta and eta rules for Σᵉ.
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

uncurry : {Δ : Tel} {A : el Δ → Type} (B : (w : el Δ) → A w → Type) → el (Δ ▸ A) → Type
uncurry B w = B (pop w) (top w)

eq-coe← : {Δ : Tel} {B : el Δ → Type} {a₀ a₁ : el Δ} (a₂ : a₀ ≡ a₁) {b₁ : B a₁} →
  (a₀ ∷ coe← (cong B a₂) b₁) ≡ (a₁ ∷ b₁)
eq-coe← reflᵉ = reflᵉ

----------------------------------------
-- Concatenation of telescopes
----------------------------------------

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
  POPε : (Δ : Tel) (w : el Δ) → POP (λ _ → ε) w ≡ w
  TOPε : (Δ : Tel) (w : el Δ) → TOP (λ _ → ε) w ≡ []
  PAIRε : (Δ : Tel) (w : el Δ) (v : el ε) → (PAIR (λ _ → ε) w v) ≡ w
  POP▸ : (Δ : Tel) (Θ : el Δ → Tel) (A : (w : el Δ) → el (Θ w) → Type)
    (w : el (Δ ► (λ v → Θ v ▸ A v))) → POP (λ v → Θ v ▸ A v) w ≡ POP Θ (pop w)

{-# REWRITE βTOP POPε TOPε PAIRε POP▸ #-}

postulate
  TOP▸ : (Δ : Tel) (Θ : el Δ → Tel) (A : (w : el Δ) → el (Θ w) → Type)
    (w : el (Δ ► (λ v → Θ v ▸ A v))) → TOP (λ v → Θ v ▸ A v) w ≡ (TOP Θ (pop w) ∷ top w)

{-# REWRITE TOP▸ #-}

postulate
  PAIR▸ : (Δ : Tel) (Θ : el Δ → Tel) (A : (w : el Δ) → el (Θ w) → Type) (w : el Δ) (v : el (Θ w ▸ A w)) →
    (PAIR (λ w → Θ w ▸ A w) w v) ≡ (PAIR Θ w (pop v)) ∷ top v

{-# REWRITE PAIR▸ #-}

PROD : Tel → Tel → Tel
PROD Δ Θ = Δ ► (λ _ → Θ)

FST : (Δ Θ : Tel) → el (PROD Δ Θ) → el Δ
FST Δ Θ w = POP (λ _ → Θ) w

SND : (Δ Θ : Tel) → el (PROD Δ Θ) → el Θ
SND Δ Θ w = TOP (λ _ → Θ) w

PR : (Δ Θ : Tel) → el Δ → el Θ → el (PROD Δ Θ)
PR Δ Θ u v = PAIR (λ _ → Θ) u v
