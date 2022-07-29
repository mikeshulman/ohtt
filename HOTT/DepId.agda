{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.DepId where

open import HOTT.Rewrite
open import HOTT.Identity
open import HOTT.Telescope
open import HOTT.Types.Sigma
open import HOTT.Types.Pi
open import HOTT.Types.Universe

----------------------------------------
-- Dependent identity types
----------------------------------------

-- Dependent on a telescope
𝕀𝕕 : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₀ : A ⊘ δ ₀) (a₁ : A ⊘ δ ₁) → Type
𝕀𝕕 {Δ} A δ a₀ a₁ = refl A ⊘ δ // a₀ ~ a₁

-- Dependent on a single type
Id : {A : Type} (B : A ⇒ Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ : B ∙ a₀) (b₁ : B ∙ a₁) → Type
Id B {a₀} {a₁} a₂ b₀ b₁ = refl B ∙ a₀ ∙ a₁ ∙ a₂ // b₀ ~ b₁


------------------------------------------------------------
-- Identity types of dependent telescope function-types
------------------------------------------------------------

postulate
  ＝ℿ : (Δ : Tel) (T : el Δ → Type) (f g : ℿ Δ T) → (f ＝ g) ≡ （ δ ⦂ ID Δ ）⇨ 𝕀𝕕 (𝚲 T) δ (f ⊘ δ ₀) (g ⊘ δ ₁)

{-# REWRITE ＝ℿ #-}
