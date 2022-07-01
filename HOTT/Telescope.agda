{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --cumulativity --no-projection-like #-}

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

data _⇨_ (Δ : Tel) (T : Typeᵉ) : Typeᵉ where
  lam-Tel : (el Δ → T) → (Δ ⇨ T)

infix 30 lam-Tel
infix 40 _⊘_
infixr 40 _⊚_ 

syntax lam-Tel (λ x → B) = Λ x ⇨ B

_⊘_ : {Δ : Tel} {T : Typeᵉ} (B : Δ ⇨ T) (x : el Δ) → T
(lam-Tel B) ⊘ x = B x

postulate
  lam-Tel-η : {Δ : Tel} {T : Typeᵉ} (A : Δ ⇨ T) → (Λ x ⇨ A ⊘ x) ≡ᵉ A

{-# REWRITE lam-Tel-η #-}

IDMAP : {Γ : Tel} → (Γ ⇨ el Γ)
IDMAP = lam-Tel (λ x → x)

postulate
  _⊚_ : {Γ Δ : Tel} {T : Typeᵉ} (g : Δ ⇨ T) (f : Γ ⇨ el Δ) → (Γ ⇨ T)
  ⊚⊘ : {Γ Δ : Tel} {T : Typeᵉ} (g : Δ ⇨ T) (f : Γ ⇨ el Δ) (x : el Γ) →
    (g ⊚ f) ⊘ x ≡ᵉ g ⊘ (f ⊘ x)
  ⊚const : {Γ Δ : Tel} {T : Typeᵉ} (A : Δ ⇨ T) (δ : el Δ) →
    _⊚_ {Γ} A (Λ _ ⇨ δ) ≡ᵉ (Λ x ⇨ A ⊘ δ)
  ⊚IDMAP : {Δ : Tel} {T : Typeᵉ} (A : Δ ⇨ T) → A ⊚ IDMAP ≡ᵉ A
  IDMAP⊚ : {Γ Δ : Tel} (f : Γ ⇨ el Δ) → _⊚_ {Γ} {Δ} {el Δ} IDMAP f ≡ᵉ f
  ⊚⊚⊚ : {Γ Δ Θ : Tel} {T : Typeᵉ} (h : Θ ⇨ T) (g : Δ ⇨ el Θ) (f : Γ ⇨ el Δ) →
    (h ⊚ g) ⊚ f ≡ᵉ h ⊚ (g ⊚ f)

{-# REWRITE ⊚⊘ ⊚const ⊚IDMAP IDMAP⊚ ⊚⊚⊚ #-}

data _▹_ (Δ : Tel) (B : Δ ⇨ Type) : Typeᵉ where
-- We name the constructor ∷ because we think of the
-- elements of a telescope as a snoc-list, and we name its projections
-- 'top' and 'pop' because we think of them as De Bruijn indices
-- accessing elements of such a list.
  _∷_ : (x : el Δ) → B ⊘ x → Δ ▹ B
open _▹_

data Tel where
  ε : Tel
  _▸_ : (Δ : Tel) (A : Δ ⇨ Type) → Tel

el ε = ⊤ᵉ
el (Δ ▸ A) = Δ ▹ A

pop : {Δ : Tel} {B : Δ ⇨ Type} → Δ ▹ B → el Δ
pop (δ ∷ _) = δ

top : {Δ : Tel} {B : Δ ⇨ Type} (δ : Δ ▹ B) → B ⊘ (pop δ)
top (_ ∷ b) = b

infixl 30 _▸_
infixl 50 _∷_

POP : {Δ : Tel} {B : Δ ⇨ Type} → ((Δ ▸ B) ⇨ el Δ)
POP = (Λ x ⇨ pop x)

uncurry : {T : Type} {Δ : Tel} {A : Δ ⇨ Type} (B : (w : el Δ) → A ⊘ w → T) → el (Δ ▸ A) → T
uncurry B w = B (pop w) (top w)

∷≡ : {Δ : Tel} (A : Δ ⇨ Type) {δ₀ δ₁ : el Δ} (e : δ₀ ≡ᵉ δ₁) {a₀ : A ⊘ δ₀} {a₁ : A ⊘ δ₁} (f : a₀ ≡ʰ a₁) →
  _≡ᵉ_ {el (Δ ▸ A)} (δ₀ ∷ a₀) (δ₁ ∷ a₁)
∷≡ A reflᵉᵉ reflʰ = reflᵉᵉ
