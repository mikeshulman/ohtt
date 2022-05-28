{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Unit where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

--------------------
-- Unit type
--------------------

record ⊤ : Type where
  constructor ★

postulate
  Id⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} {δ₂ : el (ID Δ δ₀ δ₁)} (u v : ⊤) → Id′ {Δ} (λ _ → ⊤) δ₂ u v ≡ ⊤

{-# REWRITE Id⊤ #-}

postulate
  ap★ : {Δ : Tel} {δ₀ δ₁ : el Δ} {δ₂ : el (ID Δ δ₀ δ₁)} → ap {Δ} (λ _ → ★) δ₂ ≡ ★
  -- I think Id-pop-⊤ should be a special case of Id-pop-const
  -- Id-pop-⊤ : {Δ : Tel} (X : el Δ → Type) {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁)) (a₀ a₁ : ⊤) →
  --   Id-pop X (λ _ → ⊤) δ₂ a₀ a₁ ≡ reflᵉ

{-# REWRITE ap★ #-}

----------------------------------------
-- Transport in the unit type
----------------------------------------

postulate
  tr→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤) → tr→ {Δ} (λ _ → ⊤) δ₂ a₀ ≡ a₀
  lift→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤) → lift→ {Δ} (λ _ → ⊤) δ₂ a₀ ≡ ★
  tr←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤) → tr← {Δ} (λ _ → ⊤) δ₂ a₁ ≡ a₁
  lift←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤) → lift← {Δ} (λ _ → ⊤) δ₂ a₁ ≡ ★
  utr→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤)
    (a₁ a₁' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁') →
    utr→ {Δ} (λ _ → ⊤) δ₂ a₀ a₁ a₁' a₂ a₂' ≡ ★
  ulift→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤)
    (a₁ a₁' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁') →
    ulift→ {Δ} (λ _ → ⊤) δ₂ a₀ a₁ a₁' a₂ a₂' ≡ ★
  utr←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤)
    (a₀ a₀' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀' a₁) →
    utr← {Δ} (λ _ → ⊤) δ₂ a₁ a₀ a₀' a₂ a₂' ≡ ★
  ulift←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤)
    (a₀ a₀' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀' a₁) →
    ulift← {Δ} (λ _ → ⊤) δ₂ a₁ a₀ a₀' a₂ a₂' ≡ ★

{-# REWRITE tr→⊤ lift→⊤ tr←⊤ lift←⊤ utr→⊤ ulift→⊤ utr←⊤ ulift←⊤ #-}
