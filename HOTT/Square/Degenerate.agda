{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Square.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square

----------------------------------------
-- Degenerate squares
----------------------------------------

-- Top-bottom degenerate squares in a context
DEGSQ-TB : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → el (SQ Δ δ₂ δ₂ (REFL δ₀) (REFL δ₁))
DEGSQ-TB Δ {δ₀} {δ₁} δ₂ =
  COE← (ID′-AP {Δ} {PROD Δ Δ} (λ w → PR Δ Δ w w) δ₂ (UID Δ) (REFL δ₀) (REFL δ₁))
       (AP′ {Δ} (λ w → ID Δ w w) REFL δ₂)

-- Left-right degenerate squares in a context
DEGSQ-LR : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → el (SQ Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂)
DEGSQ-LR Δ {δ₀} {δ₁} δ₂ = COE← (ID′-AP {ε} (λ _ → PR Δ Δ δ₀ δ₁) [] (UID Δ) δ₂ δ₂) (REFL δ₂)
