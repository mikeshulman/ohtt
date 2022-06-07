{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Sym where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square
open import HOTT.Square.Degenerate

------------------------------
-- Symmetry
------------------------------

postulate
  SYM : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
    (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) →
    el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁) → el (SQ Δ δ₂₀ δ₂₁ δ₀₂ δ₁₂)
  SYM-SYM : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
    (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁)) →
    SYM Δ δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) ≡ δ₂₂
  SYM-DEGSQ : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    SYM Δ δ₂ δ₂ (REFL δ₀) (REFL δ₁) (DEGSQ-TB Δ δ₂) ≡ DEGSQ-LR Δ δ₂

{-# REWRITE SYM-SYM SYM-DEGSQ #-}

postulate
  sym : {Δ : Tel} (A : el Δ → Type)
        {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
        (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
        {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
        (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
        Sq A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁ → Sq A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂ a₁₂
  sym-sym : {Δ : Tel} (A : el Δ → Type)
            {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
            (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
            {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
            (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) (a₂₂ : Sq A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁) →
            sym A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂ a₁₂ (sym A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂) ≡ a₂₂

{-# REWRITE sym-sym #-}
