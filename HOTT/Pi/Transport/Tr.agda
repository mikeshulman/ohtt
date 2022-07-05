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
    tr→ (Λ w ⇨ Π (A w) (B w)) δ f₀ ≡
    ƛ a₁ ⇒ tr→ (Λ⇨ (uncurry {Type} {Δ} {Λ⇨ A} B))
               (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁)
               (f₀ ∙ (tr← (Λ⇨ A) δ a₁))
  tr←Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₁ : Π (A (δ ₁)) (B (δ ₁))) →
    tr← (Λ w ⇨ Π (A w) (B w)) δ f₁ ≡
    ƛ a₀ ⇒ tr← (Λ⇨ (uncurry {Type} {Δ} {Λ⇨ A} B))
               (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀)
               (f₁ ∙ (tr→ (Λ⇨ A) δ a₀))

{-# REWRITE tr→Π tr←Π #-}
