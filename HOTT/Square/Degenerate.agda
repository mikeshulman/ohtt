{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Square.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Sym.Base

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

-- TODO: A version for a dependent square in a type?

----------------------------------------
-- Top-bottom degenerate squares
----------------------------------------

-- The top-bottom degenerate square is (AP REFL δ), which is supposed
-- to compute to (SYM Δ (REFL δ)).  Unfortunately, neither of these
-- have the correct boundary definitionally (for abstract telescopes;
-- they should for concrete telescopes made of concrete types).

-- As usual, we postulate the relevant computation for types and prove
-- it for telescopes.

-- TODO

  
