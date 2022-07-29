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

postulate
  ＝⇒ : (A B : Type) (f g : A ⇒ B) → (f ＝ g) ≡ （ a₀ ⦂ A ）⇒ （ a₁ ⦂ A ）⇒ (a₀ ＝ a₁) ⇒ (f ∙ a₀ ＝ g ∙ a₁)

{-# REWRITE ＝⇒ #-}

postulate
  reflƛⁿᵈ : (A B : Type) (f : A ⇒ B) →
    refl f ≡ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ refl {（ x ⦂ (ε ▸ (Λ _ ⇨ A)) ）⇨ B} (Λ x ⇨ f ∙ top x) ⊘ ([] ∷ a₀ ∷ a₁ ∷ a₂))

{-# REWRITE reflƛⁿᵈ #-}

postulate
  refl∙ⁿᵈ : (A B : Type) (f : A ⇒ B) (a : A) → refl (f ∙ a) ≡ refl f ∙ a ∙ a ∙ refl a

{-# REWRITE refl∙ⁿᵈ #-}
