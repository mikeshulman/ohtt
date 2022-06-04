{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Test where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

----------------------------------------
-- Examples for testing
----------------------------------------

postulate
  A : Type
  a₀ a₁ : A
  a₂ : Id A a₀ a₁

A′ : el ε → Type
A′ _ = A

postulate
  B : el (ε ▸ A′) → Type
  b₀ : B ([] ∷ a₀)
  b₁ : B ([] ∷ a₁)
  b₂ : Id′ B ([] ∷ a₂) b₀ b₁
  C : el (ε ▸ A′ ▸ B) → Type
  c₀ : C ([] ∷ a₀ ∷ b₀)
  c₁ : C ([] ∷ a₁ ∷ b₁)
  c₂ : Id′ C ([] ∷ a₂ ∷ b₂) c₀ c₁

-- Testing normalization of ap-top (normalize these with C-c C-n).
-- The "-A" versions compute correctly, but the others should involve
-- coercions along Id-AP; we hope that for concrete types these will
-- compute away.  At the moment the others also take too long to
-- normalize.
egA-A = ap {Δ = ε ▸ A′} (λ w → top w) {[] ∷ a₀} {[] ∷ a₁} ([] ∷ a₂)
egAB-B = ap {Δ = ε ▸ A′ ▸ B} (λ w → top w) {[] ∷ a₀ ∷ b₀} {[] ∷ a₁ ∷ b₁} ([] ∷ a₂ ∷ b₂)
egAB-A = ap {Δ = ε ▸ A′ ▸ B} (λ w → top (pop w)) {[] ∷ a₀ ∷ b₀} {[] ∷ a₁ ∷ b₁} ([] ∷ a₂ ∷ b₂)
egABC-C = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top w) {[] ∷ a₀ ∷ b₀ ∷ c₀} {[] ∷ a₁ ∷ b₁ ∷ c₁} ([] ∷ a₂ ∷ b₂ ∷ c₂)
egABC-B = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top (pop w)) {[] ∷ a₀ ∷ b₀ ∷ c₀} {[] ∷ a₁ ∷ b₁ ∷ c₁} ([] ∷ a₂ ∷ b₂ ∷ c₂)
egABC-A = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top (pop (pop w))) {[] ∷ a₀ ∷ b₀ ∷ c₀} {[] ∷ a₁ ∷ b₁ ∷ c₁} ([] ∷ a₂ ∷ b₂ ∷ c₂)
