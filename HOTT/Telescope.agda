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
-- for this is explained in the comments to ap-top.  Thus, it also has
-- to be defined mutually with Tel and el.

-- We make Σᵉ a postulate rather than a datatype because our
-- applications of rewrite rules don't work otherwise.  Specifically,
-- rewriting in Agda happens modulo eta-expansion, so if Σᵉ were a
-- record with constructor ∷, then every element of an extended
-- telescope would be considered to have the form ∷ for rewriting
-- purposes.  This would break our approach to AP on variables, where
-- we want AP to reduce on ∷ to make the telescope smaller, but to
-- reduce on pop to make the telescope *larger* until the function
-- becomes the identity.  For similar reasons, we will later use
-- postulates and rewrite rules for our actual type formers Σ, Π, etc.
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
-- 'top' and 'pop' because we think of them as De Bruijn indices
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

∷≡ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (e : δ₀ ≡ δ₁) {a₀ : A δ₀} {a₁ : A δ₁} (f : a₀ ≡ʰ a₁) →
  (δ₀ ∷ a₀) ≡ (δ₁ ∷ a₁)
∷≡ A reflᵉ reflʰ = reflᵉ
