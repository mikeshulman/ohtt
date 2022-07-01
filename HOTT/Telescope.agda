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

data _⇨_ (Δ : Tel) (T : Type) : Typeᵉ where
  Λ⇨ : (el Δ → T) → (Δ ⇨ T)

data _⇨ᵉ_ (Δ : Tel) (T : Typeᵉ) : Typeᵉ where
  Λ⇨ᵉ : (el Δ → T) → (Δ ⇨ᵉ T)

infix 30 Λ⇨ Λ⇨ᵉ

syntax Λ⇨ (λ x → B) = Λ x ⇨ B
syntax Λ⇨ᵉ (λ x → B) = Λ x ⇨ᵉ B

infix 40 _⊘_ _⊘ᵉ_

_⊘_ : {Δ : Tel} {T : Type} (B : Δ ⇨ T) (x : el Δ) → T
(Λ⇨ B) ⊘ x = B x

_⊘ᵉ_ : {Δ : Tel} {T : Typeᵉ} (B : Δ ⇨ᵉ T) (x : el Δ) → T
(Λ⇨ᵉ B) ⊘ᵉ x = B x

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

ε▸ : (A : Type) → Tel
ε▸ A = ε ▸ (Λ _ ⇨ A)

POP : {Δ : Tel} {B : Δ ⇨ Type} → ((Δ ▸ B) ⇨ᵉ el Δ)
POP = (Λ x ⇨ᵉ pop x)

uncurry : {T : Type} {Δ : Tel} {A : Δ ⇨ Type} (B : (w : el Δ) → A ⊘ w → T) → el (Δ ▸ A) → T
uncurry B w = B (pop w) (top w)

∷≡ : {Δ : Tel} (A : Δ ⇨ Type) {δ₀ δ₁ : el Δ} (e : δ₀ ≡ᵉ δ₁) {a₀ : A ⊘ δ₀} {a₁ : A ⊘ δ₁} (f : a₀ ≡ʰ a₁) →
  _≡ᵉ_ {el (Δ ▸ A)} (δ₀ ∷ a₀) (δ₁ ∷ a₁)
∷≡ A reflᵉᵉ reflʰ = reflᵉᵉ

infixr 40 _⊚_ _⊚ᵉ_

postulate
  Λ⇨η : {Δ : Tel} {T : Type} (A : Δ ⇨ T) → (Λ x ⇨ A ⊘ x) ≡ᵉ A
  Λ⇨ᵉη : {Δ : Tel} {T : Typeᵉ} (A : Δ ⇨ᵉ T) → (Λ x ⇨ᵉ A ⊘ᵉ x) ≡ᵉ A

{-# REWRITE Λ⇨η Λ⇨ᵉη #-}

IDMAP : {Γ : Tel} → (Γ ⇨ᵉ el Γ)
IDMAP = Λ x ⇨ᵉ x

postulate
  _⊚_ : {Γ Δ : Tel} {T : Type} (g : Δ ⇨ T) (f : Γ ⇨ᵉ el Δ) → (Γ ⇨ T)
  _⊚ᵉ_ : {Γ Δ : Tel} {T : Typeᵉ} (g : Δ ⇨ᵉ T) (f : Γ ⇨ᵉ el Δ) → (Γ ⇨ᵉ T)
  ⊚⊘ : {Γ Δ : Tel} {T : Type} (g : Δ ⇨ T) (f : Γ ⇨ᵉ el Δ) (x : el Γ) →
    (g ⊚ f) ⊘ x ≡ g ⊘ (f ⊘ᵉ x)
  ⊚ᵉ⊘ : {Γ Δ : Tel} {T : Typeᵉ} (g : Δ ⇨ᵉ T) (f : Γ ⇨ᵉ el Δ) (x : el Γ) →
    (g ⊚ᵉ f) ⊘ᵉ x ≡ᵉ g ⊘ᵉ (f ⊘ᵉ x)
  ⊚const : {Γ Δ : Tel} {T : Type} (A : Δ ⇨ T) (δ : el Δ) →
    _⊚_ {Γ} A (Λ _ ⇨ᵉ δ) ≡ᵉ (Λ x ⇨ A ⊘ δ)
  ⊚ᵉconst : {Γ Δ : Tel} {T : Typeᵉ} (A : Δ ⇨ᵉ T) (δ : el Δ) →
    _⊚ᵉ_ {Γ} A (Λ _ ⇨ᵉ δ) ≡ᵉ (Λ x ⇨ᵉ A ⊘ᵉ δ)
  ⊚IDMAP : {Δ : Tel} {T : Type} (A : Δ ⇨ T) → A ⊚ IDMAP ≡ᵉ A
  ⊚ᵉIDMAP : {Δ : Tel} {T : Typeᵉ} (A : Δ ⇨ᵉ T) → A ⊚ᵉ IDMAP ≡ᵉ A
  IDMAP⊚ᵉ : {Γ Δ : Tel} (f : Γ ⇨ᵉ el Δ) → _⊚ᵉ_ {Γ} {Δ} {el Δ} IDMAP f ≡ᵉ f
  ⊚⊚ᵉ⊚ᵉ : {Γ Δ Θ : Tel} {T : Type} (h : Θ ⇨ T) (g : Δ ⇨ᵉ el Θ) (f : Γ ⇨ᵉ el Δ) →
    (h ⊚ g) ⊚ f ≡ᵉ h ⊚ (g ⊚ᵉ f)
  ⊚ᵉ⊚ᵉ⊚ᵉ : {Γ Δ Θ : Tel} {T : Typeᵉ} (h : Θ ⇨ᵉ T) (g : Δ ⇨ᵉ el Θ) (f : Γ ⇨ᵉ el Δ) →
    (h ⊚ᵉ g) ⊚ᵉ f ≡ᵉ h ⊚ᵉ (g ⊚ᵉ f)

{-# REWRITE ⊚⊘ ⊚ᵉ⊘ ⊚const ⊚ᵉconst ⊚IDMAP ⊚ᵉIDMAP IDMAP⊚ᵉ ⊚⊚ᵉ⊚ᵉ ⊚ᵉ⊚ᵉ⊚ᵉ #-}
