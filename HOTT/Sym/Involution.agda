{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Involution where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Sym.Base

------------------------------
-- Symmetry is an involution
------------------------------

-- We postulate that symmetry on types is an involution, and prove
-- from this that it is an involution on telescopes.

SYM-SYM : (Δ : Tel) (δ : el (SQ Δ)) → SYM Δ (SYM Δ δ) ≡ δ

postulate
  sym-sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
    (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
    -- TODO: Hmm, is this not workable as a rewrite rule?  I think we
    -- can't reliably expect to match against SYM, since it would
    -- compute on concrete telescopes.
    sym A (SYM Δ δ) _ _ _ _ (sym A δ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂) ≡
    {! a₂₂ !}

SYM-SYM ε δ = reflᵉ
SYM-SYM (Δ ▸ A) δ = {!!}

-- {-# REWRITE sym-sym SYM-SYM #-}
