{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Universe.App.Ulift where

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
open import HOTT.Universe.App.Base
open import HOTT.Universe.App.Utr

postulate
  ulift→-∙ : {Γ : Tel} (γ : el (ID Γ)) 
    (A : el Γ → Type) (f : (x : el Γ) → A x ⇒ Type) (g : (x : el Γ) → A x)
    (x₀ : f (γ ₀) ∙ g (γ ₀)) (x₁ x₁' : f (γ ₁) ∙ g (γ ₁))
    (x₂ : Id (Λ x ⇨ f x ∙ g x) γ x₀ x₁) (x₂' : Id (Λ x ⇨ f x ∙ g x) γ x₀ x₁') →
    ulift→ (Λ x ⇨ f x ∙ g x) γ x₀ x₁ x₁' x₂ x₂' ≡
    u~coe⇒ (top (AP {Γ} {Γ ▸ (Λ _ ⇨ Type)} (Λ x ⇨ᵉ x ∷ f x ∙ g x) γ)) x₀ x₁ x₁' x₂ x₂'
  ulift←-∙ : {Γ : Tel} (γ : el (ID Γ)) 
    (A : el Γ → Type) (f : (x : el Γ) → A x ⇒ Type) (g : (x : el Γ) → A x)
    (x₁ : f (γ ₁) ∙ g (γ ₁)) (x₀ x₀' : f (γ ₀) ∙ g (γ ₀))
    (x₂ : Id (Λ x ⇨ f x ∙ g x) γ x₀ x₁) (x₂' : Id (Λ x ⇨ f x ∙ g x) γ x₀' x₁) →
    ulift← (Λ x ⇨ f x ∙ g x) γ x₁ x₀ x₀' x₂ x₂' ≡
    u~coe⇐ (top (AP {Γ} {Γ ▸ (Λ _ ⇨ Type)} (Λ x ⇨ᵉ x ∷ f x ∙ g x) γ)) x₁ x₀ x₀' x₂ x₂'

{-# REWRITE ulift→-∙ ulift←-∙ #-}
