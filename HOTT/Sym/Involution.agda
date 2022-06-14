{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Involution where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square
open import HOTT.Sym

------------------------------
-- Symmetry is an involution
------------------------------

-- Similarly, we postulate that symmetry on types is an involution,
-- and prove from this that it is an involution on telescopes.

{-
SYM-SYM : (Δ : Tel) (δ : el (SQ Δ)) → SYM Δ (SYM Δ δ) ≡ δ

postulate
  sym-sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
        {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
        {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
        (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
        sym A (SYM Δ δ) a₂₀ a₂₁ a₀₂ a₁₂ (sym A δ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂) ≡ a₂₂

SYM-SYM Δ δ = {!!}

-- {-# REWRITE sym-sym SYM-SYM #-}
-}
