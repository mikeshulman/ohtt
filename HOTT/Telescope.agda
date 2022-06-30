{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-projection-like #-}

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

-- We make _▹_ a datatype rather than a record because our applications
-- of rewrite rules don't work otherwise.  There are at least two
-- reasons for this:

-- 1. Rewriting in Agda happens modulo eta-expansion for records.
-- Thus, if _▹_ were a record with constructor ∷, then every element of
-- an extended telescope would be considered to have the form ∷ for
-- rewriting purposes.  This would break our approach to AP on
-- variables, where we want AP to reduce on ∷ to make the telescope
-- smaller, but to reduce on pop to make the telescope *larger* until
-- the function becomes the identity.

-- 2. Our rewrite rules need to match against pop and top (notably
-- AP-pop and ap-top).  But this doesn't work if pop and top are
-- projections, since then Agda doesn't consider their argument to be
-- bound by such a LHS pattern.

-- For similar reasons, we will later use datatypes and rewrite rules
-- for our actual type formers Σ, Π, etc.

data _→Type (Δ : Tel) : Typeᵉ where
  lam-Tel : (el Δ → Type) → (Δ →Type)

infix 30 lam-Tel
infix 40 _⊘_

syntax lam-Tel (λ x → B) = Λ x ⇒ B

_⊘_ : {Δ : Tel} (B : Δ →Type) (x : el Δ) → Type
(lam-Tel B) ⊘ x = B x

postulate
  lam-Tel-η : {Δ : Tel} (A : Δ →Type) → (Λ x ⇒ A ⊘ x) ≡ᵉ A

{-# REWRITE lam-Tel-η #-}

data _▹_ (Δ : Tel) (B : Δ →Type) : Typeᵉ where
-- We name the constructor ∷ because we think of the
-- elements of a telescope as a snoc-list, and we name its projections
-- 'top' and 'pop' because we think of them as De Bruijn indices
-- accessing elements of such a list.
  _∷_ : (x : el Δ) → B ⊘ x → Δ ▹ B
open _▹_

pop : {Δ : Tel} {B : Δ →Type} → Δ ▹ B → el Δ
pop (δ ∷ _) = δ

top : {Δ : Tel} {B : Δ →Type} (δ : Δ ▹ B) → B ⊘ pop δ
top (_ ∷ b) = b

data Tel where
  ε : Tel
  _▸_ : (Δ : Tel) (A : Δ →Type) → Tel

el ε = ⊤ᵉ
el (Δ ▸ A) = Δ ▹ A

infixl 30 _▸_ _∷_

data _⇨_ (Γ Δ : Tel) : Typeᵉ where
  lam-Sub : (el Γ → el Δ) → (Γ ⇨ Δ)

syntax lam-Sub (λ x → B) = Λ x ⇨ B

infix 40 _∘_ _⊛_

_∘_ : {Γ Δ Θ : Tel} (g : Δ ⇨ Θ) (f : Γ ⇨ Δ) → (Γ ⇨ Θ)
(lam-Sub g ∘ lam-Sub f) = lam-Sub (λ x → g (f x))

_⊛_ : {Γ Δ : Tel} (f : Γ ⇨ Δ) → el Γ → el Δ
(lam-Sub f) ⊛ x = f x

postulate
  lam-Sub-η : {Γ Δ : Tel} (f : Γ ⇨ Δ) → (Λ x ⇨ f ⊛ x) ≡ᵉ f

{-# REWRITE lam-Sub-η #-}


IDMAP : {Γ : Tel} → (Γ ⇨ Γ)
IDMAP = lam-Sub (λ x → x)

POP : {Δ : Tel} {B : Δ →Type} → ((Δ ▸ B) ⇨ Δ)
POP = (Λ x ⇨ pop x)

_⊚_ : {Γ Δ : Tel} (A : Δ →Type) (f : Γ ⇨ Δ) → (Γ →Type)
(lam-Tel A) ⊚ (lam-Sub f) = lam-Tel (λ x → A (f x))

postulate
  ⊚⊘ : {Γ Δ : Tel} (A : Δ →Type) (f : Γ ⇨ Δ) (γ : el Γ) →
    (A ⊚ f) ⊘ γ ≡ A ⊘ (f ⊛ γ)
  ⊚const : {Γ Δ : Tel} (A : Δ →Type) (δ : el Δ) →
    _⊚_ {Γ} A (Λ _ ⇨ δ) ≡ᵉ Λ x ⇒ A ⊘ δ
  ⊚IDMAP : {Δ : Tel} (A : Δ →Type) → A ⊚ IDMAP ≡ᵉ A

{-# REWRITE ⊚⊘ ⊚const ⊚IDMAP #-}

uncurry : {T : Type} {Δ : Tel} {A : Δ →Type} (B : (w : el Δ) → A ⊘ w → T) → el (Δ ▸ A) → T
uncurry B w = B (pop w) (top w)

∷≡ : {Δ : Tel} (A : Δ →Type) {δ₀ δ₁ : el Δ} (e : δ₀ ≡ᵉ δ₁) {a₀ : A ⊘ δ₀} {a₁ : A ⊘ δ₁} (f : a₀ ≡ʰ a₁) →
  _≡ᵉ_ {el (Δ ▸ A)} (δ₀ ∷ a₀) (δ₁ ∷ a₁)
∷≡ A reflᵉᵉ reflʰ = reflᵉᵉ
