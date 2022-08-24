{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Types.Pi where

open import HOTT.Rewrite
open import HOTT.Identity
open import HOTT.Telescope

infixl 40 _∙_
infixr 30 _⇒_ Π
infixr 20 𝛌
infixl 40 _∘_

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

--------------------------------------------------
-- Identity types of non-dependent function types
--------------------------------------------------

-- We will give all the rules involving identity types for Π-types in
-- Pi2, after we have dependent identity types defined using the
-- universe.  However, defining all of that requires already knowing
-- identity types of *non-dependent* function types, and a bit of
-- computation for them, so we give those here.  They will later be
-- subsumed by the rules in Pi2.

postulate
  ＝⇒ : (A B : Type) (f g : A ⇒ B) → (f ＝ g) ≡ （ a₀ ⦂ A ）⇒ （ a₁ ⦂ A ）⇒ (a₀ ＝ a₁) ⇒ (f ∙ a₀ ＝ g ∙ a₁)

{-# REWRITE ＝⇒ #-}

postulate
{-
  refl-ƛⁿᵈ : (A B : Type) (f : A → B) →
    refl (𝛌 f) ≡ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒
    refl {（ x ⦂ (ε ▸ (Λ _ ⇨ A)) ）⇨ B} (Λ x ⇨ f (top x)) ⊘ ([] ∷ a₀ ∷ a₁ ∷ a₂))
-}
  refl-ƛⁿᵈ : (A B : Type) (f : A → B) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    refl (𝛌 f) ∙ a₀ ∙ a₁ ∙ a₂ ≡
    refl {（ x ⦂ (ε ▸ (Λ _ ⇨ A)) ）⇨ B} (Λ x ⇨ f (top x)) ⊘ ([] ∷ a₀ ∷ a₁ ∷ a₂)

{-# REWRITE refl-ƛⁿᵈ #-}

postulate
  refl-∙ⁿᵈ : (A B : Type) (f : A ⇒ B) (a : A) → refl (f ∙ a) ≡ refl f ∙ a ∙ a ∙ refl a

{-# REWRITE refl-∙ⁿᵈ #-}