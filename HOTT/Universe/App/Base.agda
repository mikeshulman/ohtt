{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Universe.App.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Sigma
open import HOTT.Pi
open import HOTT.Copy
open import HOTT.Groupoids
open import HOTT.Universe.Base

postulate
  Id-∙ : {Γ : Tel} (γ : el (ID Γ))
    (A : el Γ → Type) (f : (x : el Γ) → A x ⇒ Type) (g : (x : el Γ) → A x)
    (x₀ : f (γ ₀) ∙ g (γ ₀)) (x₁ : f (γ ₁) ∙ g (γ ₁)) →
    Id (Λ x ⇨ f x ∙ g x) γ x₀ x₁ ≡
    (x₀ ~[ top (AP {Γ} {Γ ▸ (Λ _ ⇨ Type)} (Λ x ⇨ᵉ x ∷ f x ∙ g x) γ) ] x₁)

{-# REWRITE Id-∙ #-}
