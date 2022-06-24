{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Pi.Transport.Tr where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Transport
open import HOTT.Pi.Base

postulate
  tr→Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₀ : Π (A (δ ₀)) (B (δ ₀))) →
    tr→ (λ w → Π (A w) (B w)) δ f₀ ≡
    Λ a₁ ⇛ tr→ (uncurry B) (δ ∷ tr← A δ a₁ ∷ a₁ ∷ lift← A δ a₁) (f₀ ⊙ (tr← A δ a₁))
  tr←Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₁ : Π (A (δ ₁)) (B (δ ₁))) →
    tr← (λ w → Π (A w) (B w)) δ f₁ ≡
    Λ a₀ ⇛ tr← (uncurry B) (δ ∷ a₀ ∷ tr→ A δ a₀ ∷ lift→ A δ a₀) (f₁ ⊙ (tr→ A δ a₀))

{-# REWRITE tr→Π tr←Π #-}
