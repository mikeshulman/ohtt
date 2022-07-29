{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Types.Pi2 where

open import HOTT.Rewrite
open import HOTT.Identity
open import HOTT.Telescope
open import HOTT.Types.Pi
open import HOTT.Types.Universe
open import HOTT.DepId

--------------------------------------------------
-- Identity types of dependent Π-types
--------------------------------------------------

postulate
  ＝Π : (A : Type) (B : A → Type) (f g : Π A B) →
    (f ＝ g) ≡ （ a₀ ⦂ A ）⇒ （ a₁ ⦂ A ）⇒ （ a₂ ⦂ a₀ ＝ a₁ ）⇒ Id (𝛌 B) a₂ (f ∙ a₀) (g ∙ a₁)
{-# REWRITE ＝Π #-}

postulate
  reflƛ : (A : Type) (B : A → Type) (f : Π A B) →
    refl f ≡ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ refl {（ x ⦂ (ε ▸ (Λ _ ⇨ A)) ）⇨ B (top x)} (Λ x ⇨ f ∙ top x) ⊘ ([] ∷ a₀ ∷ a₁ ∷ a₂))

{-# REWRITE reflƛ #-}
