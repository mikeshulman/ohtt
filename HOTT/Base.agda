{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Base where

open import Agda.Primitive renaming (Set to Type; SSet to Typeᵉ) public

infixl 40 _∙_  _∘_
infixr 35 _×_
infixr 30 _,_ Σ _⇒_ Π
infixr 20 𝛌
infix  10 _≡_ _≡ᵉ_

------------------------------
-- Strict equality
------------------------------

-- Because we don't assume cumulativity, we have two strict
-- equalities, one for elements of types and one for elements of
-- exotypes.  We decorate operations involving the first with ᶠ (for
-- fibrant) and the second with ᵉ.  The exception is the equality type
-- itself, where we write ≡ instead of ≡ᶠ.

data _≡_ {A : Type} (a : A) : A → Typeᵉ where
  instance
    reflᵉ : a ≡ a
data _≡ᵉ_ {A : Typeᵉ} (a : A) : A → Typeᵉ where
  instance
    reflᵉᵉ : a ≡ᵉ a
{-# BUILTIN REWRITE _≡_ #-}
{-# BUILTIN REWRITE _≡ᵉ_ #-}

happlyᵉ : {A : Type} {B : A → Type} {f g : (x : A) → B x} →
  (f ≡ g) → ((x : A) → f x ≡ g x)
happlyᵉ reflᵉ = λ x → reflᵉ

postulate
  funextᵉ : {A : Type} {B : A → Type} {f g : (x : A) → B x} →
    ((x : A) → f x ≡ g x) → (f ≡ g)
  happlyᵉ-funextᵉ : {A : Type} {B : A → Type} {f g : (x : A) → B x} →
    (p : (x : A) → f x ≡ g x) →
    happlyᵉ (funextᵉ p) ≡ᵉ p
  funextᵉ-reflᵉ : {A : Type} {B : A → Type} (f : (x : A) → B x) →
    funextᵉ {f = f} (λ x → reflᵉ) ≡ᵉ reflᵉ
{-# REWRITE happlyᵉ-funextᵉ funextᵉ-reflᵉ #-}

--------------------
-- Unit type
--------------------

record ⊤ : Type where
  constructor ★
open ⊤

--------------------
-- Σ-types
--------------------

-- Making this a datatype rather than a postulate leads to immense
-- speedups, probably because the parameters A and B aren't carried
-- around with each instance of _,_.  It also enables more rewrites to
-- fire, because the beta-rules for fst and snd don't have to match
-- the (nonexistent) parameters on _,_.  This choice does prevent us
-- from having an η-rule, since η-contraction violates the linearity
-- restriction in parameters, but at the moment that seems a small
-- price to pay.  (We can't make it a record, since then rewrite rules
-- like ap-fst wouldn't be allowed.)
data Σ (A : Type) (B : A → Type) : Type where
  _,_ : (a : A) → B a → Σ A B
syntax Σ A (λ x → B) = （ x ⦂ A ）× B
fst : {A : Type} {B : A → Type} → Σ A B → A
fst (a , _) = a

snd : {A : Type} {B : A → Type} (u : Σ A B) → B (fst u)
snd (_ , b) = b

--  Ση : (A : Type) (B : A → Type) (u : Σ A B) → (fst u , snd u) ≡ u
-- {-# REWRITE Ση #-}

-- We can't have a definitional η-rule, but we can postulate η as an
-- exo-equality, and stipulate that this equality becomes reflexivity
-- on pairs (for which the η-rule does hold definitionally).  This way
-- the coercions along η will vanish in most concrete computations.
postulate
  ηΣ : {A : Type} (B : A → Type) (u : Σ A B) → (fst u , snd u) ≡ u
  ηΣ-, : {A : Type} (B : A → Type) (a : A) (b : B a) →
    ηΣ B (a , b) ≡ᵉ reflᵉ
{-# REWRITE ηΣ-, #-}

₁st : {A : Type} {B : A → Type} → （ x ⦂ A ）× B x → A
₁st u = fst u

₂nd' : {A : Type} {B : A → Type} → (u : （ x ⦂ A ）× B x) → B (₁st u)
₂nd' u = snd u

₂nd : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× C x y) → B (₁st u)
₂nd u = fst (snd u)

₃rd' : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× C x y) → C (₁st u) (₂nd u)
₃rd' u = snd (snd u)

₃rd : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} {D : (x : A) (y : B x) → C x y → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× （ z ⦂ C x y ）× D x y z) → C (₁st u) (₂nd u)
₃rd u = fst (snd (snd u))

₄th' : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} {D : (x : A) (y : B x) → C x y → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× （ z ⦂ C x y ）× D x y z) → D (₁st u) (₂nd u) (₃rd u)
₄th' u = snd (snd (snd u))

₄th : {A : Type} {B : A → Type} {C : (x : A) → B x → Type}
  {D : (x : A) (y : B x) → C x y → Type} {E : (x : A) (y : B x) (z : C x y) → D x y z → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× （ z ⦂ C x y ）× （ w ⦂ D x y z ）× E x y z w) →
  D (₁st u) (₂nd u) (₃rd u)
₄th u = fst (snd (snd (snd u)))

₅th' : {A : Type} {B : A → Type} {C : (x : A) → B x → Type}
  {D : (x : A) (y : B x) → C x y → Type} {E : (x : A) (y : B x) (z : C x y) → D x y z → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× （ z ⦂ C x y ）× （ w ⦂ D x y z ）× E x y z w) →
  E (₁st u) (₂nd u) (₃rd u) (₄th u)
₅th' u = snd (snd (snd (snd u)))

----------------------------------------
-- Non-dependent product types
----------------------------------------

_×_ : Type → Type → Type
A × B = （ _ ⦂ A ）× B

--------------------
-- Π-types
--------------------

postulate
  Π : (A : Type) (B : A → Type) → Type
  𝛌 : {A : Type} {B : A → Type} (f : (x : A) → B x) → Π A B
syntax Π A (λ x → B) = （ x ⦂ A ）⇒ B
syntax 𝛌 (λ x → f) = ƛ x ⇒ f

-- It's tempting to try to make Π a record type, with 𝛌 a constructor
-- and _∙_ a field.  But then _∙_ doesn't store A and B as implicit
-- arguments, which means that refl-∙ can't bind them.
postulate
  -- TODO: Add a (strict) equality to _∙_ so that rules like refl-ƛ can fire.
  _∙_ : {A : Type} {B : A → Type} (f : Π A B) (a : A) → B a
  Πβ : {A : Type} {B : A → Type} (f : (x : A) → B x) (a : A) → (𝛌 f ∙ a) ≡ f a
  Πη : {A : Type} {B : A → Type} (f : Π A B) → (ƛ x ⇒ f ∙ x) ≡ f
{-# REWRITE Πβ Πη #-}

----------------------------------------
-- Non-dependent function types
----------------------------------------

_⇒_ : Type → Type → Type
A ⇒ B = （ x ⦂ A ）⇒ B

_∘_ : {A B C : Type} (g : B ⇒ C) (f : A ⇒ B) → (A ⇒ C)
g ∘ f = ƛ x ⇒ g ∙ (f ∙ x)

idmap : (A : Type) → (A ⇒ A)
idmap A = ƛ x ⇒ x
