{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Square.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base

----------------------------------------
-- Left-right degenerate squares
----------------------------------------

-- The left-right degenerate square is just REFL.

DEGSQ-LR : {Δ : Tel} (δ : el (ID Δ)) → el (SQ Δ)
DEGSQ-LR δ = REFL δ

-- Its boundaries are correct definitionally.

DEGSQ-LR₀₂ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-LR δ ₀₂ ≡ REFL (δ ₀)
DEGSQ-LR₀₂ δ = reflᵉ

DEGSQ-LR₁₂ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-LR δ ₁₂ ≡ REFL (δ ₁)
DEGSQ-LR₁₂ δ = reflᵉ

DEGSQ-LR₂₀ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-LR δ ₂₀ ≡ δ
DEGSQ-LR₂₀ δ = reflᵉ

DEGSQ-LR₂₁ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-LR δ ₂₁ ≡ δ
DEGSQ-LR₂₁ δ = reflᵉ

----------------------------------------
-- Top-bottom degenerate squares
----------------------------------------

-- The top-bottom degenerate square is (AP REFL δ).

DEGSQ-TB : {Δ : Tel} (δ : el (ID Δ)) → el (SQ Δ)
DEGSQ-TB δ = AP REFL δ

-- Its boundaries are also correct definitionally.

DEGSQ-TB₀₂ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-TB δ ₀₂ ≡ δ
DEGSQ-TB₀₂ δ = AP-AP REFL _₀ δ

DEGSQ-TB₁₂ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-TB δ ₁₂ ≡ δ
DEGSQ-TB₁₂ δ = AP-AP REFL _₁ δ

DEGSQ-TB₂₀ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-TB δ ₂₀ ≡ REFL (δ ₀)
DEGSQ-TB₂₀ δ = reflᵉ

DEGSQ-TB₂₁ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-TB δ ₂₁ ≡ REFL (δ ₁)
DEGSQ-TB₂₁ δ = reflᵉ
