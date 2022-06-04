{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

------------------------------
-- Transport
------------------------------

postulate
  tr→ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀) → A δ₁
  lift→ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀) → Id′ A δ₂ a₀ (tr→ A δ₂ a₀)
  tr← : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A δ₁) → A δ₀
  lift← : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A δ₁) → Id′ A δ₂ (tr← A δ₂ a₁) a₁
  utr→ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀)
    (a₁ a₁' : A δ₁) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') → Id (A δ₁) a₁ a₁'
  ulift→ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀)
    (a₁ a₁' : A δ₁) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') →
    Id′ {ε ▸ (λ _ → A δ₁)} (λ w → Id′ A δ₂ a₀ (top w)) {[] ∷ a₁} {[] ∷ a₁'} ([] ∷ utr→ A δ₂ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  utr← : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A δ₁)
    (a₀ a₀' : A δ₀) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀' a₁) → Id (A δ₀) a₀ a₀'
  ulift← : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A δ₁)
    (a₀ a₀' : A δ₀) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀' a₁) →
    Id′ {ε ▸ (λ _ → A δ₀)} (λ w → Id′ A δ₂ (top w) a₁) {[] ∷ a₀} {[] ∷ a₀'} ([] ∷ utr← A δ₂ a₁ a₀ a₀' a₂ a₂') a₂ a₂'

-- TODO: Ugh, I suppose these need all the same rules as Id′?
