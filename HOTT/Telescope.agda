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
-- for this is explained in the comments to ap-top.  Thus, this sort
-- of Σ-exotype also has to be defined mutually with Tel and el.

-- We make Σᵉ a postulate rather than a datatype because our
-- applications of rewrite rules don't work otherwise.  There are at
-- least two reasons for this:

-- 1. Rewriting in Agda happens modulo eta-expansion for records.
-- Thus, if Σᵉ were a record with constructor ∷, then every element of
-- an extended telescope would be considered to have the form ∷ for
-- rewriting purposes.  This would break our approach to AP on
-- variables, where we want AP to reduce on ∷ to make the telescope
-- smaller, but to reduce on pop to make the telescope *larger* until
-- the function becomes the identity.

-- 2. Our rewrite rules need to match against pop and top (notably
-- AP-pop and ap-top).  But this doesn't work if pop and top are
-- projections, since then Agda doesn't consider their argument to be
-- bound by such a LHS pattern.

-- For similar reasons, we will later use postulates and rewrite rules
-- for our actual type formers Σ, Π, etc.
data Σᵉ (Δ : Tel) (B : el Δ → Type) : Typeᵉ where
-- We name the constructor ∷ because we think of the
-- elements of a telescope as a snoc-list, and we name its projections
-- 'top' and 'pop' because we think of them as De Bruijn indices
-- accessing elements of such a list.
  _∷_ : (x : el Δ) → B x → Σᵉ Δ B
open Σᵉ

pop : {Δ : Tel} {B : el Δ → Type} → Σᵉ Δ B → el Δ
pop (δ ∷ _) = δ

top : {Δ : Tel} {B : el Δ → Type} (δ : Σᵉ Δ B) → B (pop δ)
top (_ ∷ b) = b

data Tel where
  ε : Tel
  _▸_ : (Δ : Tel) (A : el Δ → Type) → Tel

el ε = ⊤ᵉ
el (Δ ▸ A) = Σᵉ Δ A

infixl 30 _▸_ _∷_

uncurry : {T : Type} {Δ : Tel} {A : el Δ → Type} (B : (w : el Δ) → A w → T) → el (Δ ▸ A) → T
uncurry B w = B (pop w) (top w)

∷≡ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (e : δ₀ ≡ δ₁) {a₀ : A δ₀} {a₁ : A δ₁} (f : a₀ ≡ʰ a₁) →
  (δ₀ ∷ a₀) ≡ (δ₁ ∷ a₁)
∷≡ A reflᵉ reflʰ = reflᵉ
