{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

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

DEGSQ-LR₀₂ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-LR δ ₀₂ ≡ᵉ REFL (δ ₀)
DEGSQ-LR₀₂ δ = reflᵉᵉ

DEGSQ-LR₁₂ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-LR δ ₁₂ ≡ᵉ REFL (δ ₁)
DEGSQ-LR₁₂ δ = reflᵉᵉ

DEGSQ-LR₂₀ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-LR δ ₂₀ ≡ᵉ δ
DEGSQ-LR₂₀ δ = reflᵉᵉ

DEGSQ-LR₂₁ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-LR δ ₂₁ ≡ᵉ δ
DEGSQ-LR₂₁ δ = reflᵉᵉ

----------------------------------------
-- Top-bottom degenerate squares
----------------------------------------

-- The top-bottom degenerate square is (AP REFL δ).

DEGSQ-TB : {Δ : Tel} (δ : el (ID Δ)) → el (SQ Δ)
DEGSQ-TB δ = AP ΛREFL δ

-- Two of its boundaries are also correct definitionally.

DEGSQ-TB₂₀ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-TB δ ₂₀ ≡ᵉ REFL (δ ₀)
DEGSQ-TB₂₀ δ = reflᵉᵉ

DEGSQ-TB₂₁ : {Δ : Tel} (δ : el (ID Δ)) → DEGSQ-TB δ ₂₁ ≡ᵉ REFL (δ ₁)
DEGSQ-TB₂₁ δ = reflᵉᵉ

-- The others *should* be correct definitionally, but Agda can't check that without help because AP-AP rewrites in the other direction.  We need perhaps an "AP⊚"?

DEGSQ-TB₀₂ : {Δ : Tel} (δ : el (ID Δ)) → AP Λ₀ (DEGSQ-TB δ) ≡ᵉ δ
DEGSQ-TB₀₂ δ = revᵉ (AP-AP ΛREFL Λ₀ δ) 

DEGSQ-TB₁₂ : {Δ : Tel} (δ : el (ID Δ)) → AP Λ₁ (DEGSQ-TB δ) ≡ᵉ δ
DEGSQ-TB₁₂ δ = revᵉ (AP-AP ΛREFL Λ₁ δ)

{-# REWRITE DEGSQ-TB₀₂ DEGSQ-TB₁₂ #-}
