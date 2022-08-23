{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Telescope where

open import HOTT.Rewrite
open import HOTT.Identity
open import HOTT.Types.Unit

infixl 30 _∷_
infixl 40 _⊘_
infixl 30 _▸_ _▹_
infix 20 𝚲
infix 20 ℿ
infix 60 _₀ _₁

------------------------------
-- Unit exotype
------------------------------

record ⊤ᵉ : Typeᵉ where
  constructor []
open ⊤ᵉ

--------------------------------------------------
-- Telescope exo-types and functions on them
--------------------------------------------------

-- A telescope is a list of dependent types.
data Tel : Typeᵉ

-- The elements of a telescope are defined by mutual
-- induction-recursion with the type Tel.
el : Tel → Typeᵉ

-- We introduce special datatypes for functions out of telescopes.
-- This enables a more useful kind of pattern-matching for rewrites.
postulate
  ℿ : (Δ : Tel) (T : el Δ → Type) → Type
  𝚲 : {Δ : Tel} {T : el Δ → Type} → ((x : el Δ) → T x) → ℿ Δ T

syntax ℿ Δ (λ x → T) = （ x ⦂ Δ ）⇨ T
syntax 𝚲 (λ x → f) = Λ x ⇨ f

postulate
  _⊘_ : {Δ : Tel} {T : el Δ → Type} (f : （ x ⦂ Δ ）⇨ T x) (a : el Δ) → T a
  ℿβ : {Δ : Tel} {T : el Δ → Type} (f : (x : el Δ) → T x) (a : el Δ) → (𝚲 {Δ} f) ⊘ a ≡ f a
  ℿη : {Δ : Tel} {T : el Δ → Type} (f : （ x ⦂ Δ ）⇨ T x) → 𝚲 (λ x → f ⊘ x) ≡ f 

{-# REWRITE ℿβ ℿη #-}
  
_⇨_ : Tel → Type → Type
Δ ⇨ T = （ _ ⦂ Δ ）⇨ T

-- The definition of "el" involves a sort of Σ-exotype.  But rather
-- than make this a generic Σ-exotype, we make its first argument a
-- Tel, with the second argument depending on the first via el.  The
-- reason for this is explained in the comments to ap-top.  Thus, this
-- sort of Σ-exotype also has to be defined mutually with Tel and el.

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

-- Note that the type we extend by belongs to our datatype
-- function-space.  This is why we had to define that mutually.
postulate
  _▹_ : (Δ : Tel) (B : Δ ⇨ Type) → Typeᵉ
  -- We name the constructor ∷ because we think of the elements of a
  -- telescope as a snoc-list.
  _∷_ : {Δ : Tel} {B : Δ ⇨ Type} (x : el Δ) → B ⊘ x → Δ ▹ B
  -- We name the projections of the Σ-type ▹ 'top' and 'pop', thinking
  -- of them as De Bruijn indices accessing elements of such a list.
  pop : {Δ : Tel} {B : Δ ⇨ Type} → Δ ▹ B → el Δ
  top : {Δ : Tel} {B : Δ ⇨ Type} (δ : Δ ▹ B) → B ⊘ (pop δ)
  popβ : {Δ : Tel} {B : Δ ⇨ Type} (δ : el Δ) (b : B ⊘ δ) → pop {Δ} {B} (δ ∷ b) ≡ᵉ δ

{-# REWRITE popβ #-}

postulate
  topβ : {Δ : Tel} {B : Δ ⇨ Type} (δ : el Δ) (b : B ⊘ δ) → top {Δ} {B} (δ ∷ b) ≡ b

{-# REWRITE topβ #-}

data Tel where
  ε : Tel
  _▸_ : (Δ : Tel) (A : Δ ⇨ Type) → Tel

el ε = ⊤ᵉ
el (Δ ▸ A) = Δ ▹ A

----------------------------------------
-- Auxiliary functions on telescopes
----------------------------------------

-- Some useful abbreviations

ε▸ : (A : Type) → Tel
ε▸ A = ε ▸ (Λ _ ⇨ A)

{-
POP : {Δ : Tel} {B : Δ ⇨ Type} → ((Δ ▸ B) ⇨ᵉ el Δ)
POP = (Λ x ⇨ᵉ pop x)

IDMAP : {Γ : Tel} → (Γ ⇨ᵉ el Γ)
IDMAP = Λ x ⇨ᵉ x
-}

uncurry : {T : Type} {Δ : Tel} {A : Δ ⇨ Type} (B : (w : el Δ) → A ⊘ w → T) → el (Δ ▸ A) → T
uncurry B w = B (pop w) (top w)

∷≡ : {Δ : Tel} (A : Δ ⇨ Type) {δ₀ δ₁ : el Δ} (e : δ₀ ≡ᵉ δ₁) {a₀ : A ⊘ δ₀} {a₁ : A ⊘ δ₁} (f : a₀ ≡ʰ a₁) →
  _≡ᵉ_ {el (Δ ▸ A)} (δ₀ ∷ a₀) (δ₁ ∷ a₁)
∷≡ A reflᵉᵉ reflʰ = reflᵉᵉ

{-
-- We "define" composition ⊚ of our telescope function-spaces.  However,
-- to preserve better rewrite matching, we don't actually *define* it,
-- but postulate it, with rewrites specifying its expected behavior.

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

-- It would be nice to have const-⊚ as well, as it might avoid the
-- need for Universe/TopCompose.  But currently, if we postulate
-- const-⊚ as a rewrite, we run into the above-mentioned
-- subject-reduction problem with Λη in some places.
-}

--------------------------------------------------------------------------------
-- Identity types of telescopes and non-dependent telescope function-types
--------------------------------------------------------------------------------

postulate
  ID : Tel → Tel
  IDε : ID ε ≡ᵉ ε
  ID▸ⁿᵈ : (Δ : Tel) (A : Type) →
    ID (Δ ▸ (Λ _ ⇨ A)) ≡ᵉ (ID Δ ▸ (Λ _ ⇨ A) ▸ (Λ _ ⇨ A) ▸ (Λ x ⇨ top (pop x) ＝ top x))

{-# REWRITE IDε ID▸ⁿᵈ #-}

postulate
  _₀ : {Δ : Tel} → el (ID Δ) → el Δ
  []₀ : [] ₀ ≡ᵉ []
  _₁ : {Δ : Tel} → el (ID Δ) → el Δ
  []₁ : [] ₁ ≡ᵉ []

{-# REWRITE []₀ []₁ #-}

postulate
  ▸₀ⁿᵈ : (Δ : Tel) (A : Type) (δ : el (ID Δ)) (a₀ a₁ : A) (a₂ : a₀ ＝ a₁) →
    (_₀ {Δ ▸ (Λ _ ⇨ A)} (δ ∷ a₀ ∷ a₁ ∷ a₂)) ≡ᵉ (δ ₀ ∷ a₀)
  ▸₁ⁿᵈ : (Δ : Tel) (A : Type) (δ : el (ID Δ)) (a₀ a₁ : A) (a₂ : a₀ ＝ a₁) →
    (_₁ {Δ ▸ (Λ _ ⇨ A)} (δ ∷ a₀ ∷ a₁ ∷ a₂)) ≡ᵉ (δ ₁ ∷ a₁)
  ε▸₀ⁿᵈ : (A : Type) (a₀ a₁ : A) (a₂ : a₀ ＝ a₁) →
    (_₀ {ε ▸ (Λ _ ⇨ A)} ([] ∷ a₀ ∷ a₁ ∷ a₂)) ≡ᵉ ([] ∷ a₀)
  ε▸₁ⁿᵈ : (A : Type) (a₀ a₁ : A) (a₂ : a₀ ＝ a₁) →
    (_₁ {ε ▸ (Λ _ ⇨ A)} ([] ∷ a₀ ∷ a₁ ∷ a₂)) ≡ᵉ ([] ∷ a₁)

{-# REWRITE ▸₀ⁿᵈ ▸₁ⁿᵈ ε▸₀ⁿᵈ ε▸₁ⁿᵈ #-}

postulate
  ＝⇨ : (Δ : Tel) (T : Type) (f g : Δ ⇨ T) → (f ＝ g) ≡ （ x ⦂ ID Δ ）⇨ f ⊘ x ₀ ＝ g ⊘ x ₁

{-# REWRITE ＝⇨ #-}

-- refl on telescope function-types computes on the structure of its
-- abstraction.  The base cases are variables and constant terms.

postulate
  ap-const : (Δ : Tel) (T : Type) (t : T) → refl {（ x ⦂ Δ ）⇨ T} (Λ _ ⇨ t) ≡ Λ _ ⇨ refl t

{-# REWRITE ap-const #-}
