{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Test where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl

----------------------------------------
-- Examples for testing
----------------------------------------

postulate
  A : Type
  a₀ a₁ : A
  a₂ : a₀ ＝ a₁

A′ : el ε → Type
A′ _ = A

postulate
  B : el (ε ▸ A′) → Type
  b₀ : B ([] ∷ a₀)
  b₁ : B ([] ∷ a₁)
  b₂ : Id B ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁
  C : el (ε ▸ A′ ▸ B) → Type
  c₀ : C ([] ∷ a₀ ∷ b₀)
  c₁ : C ([] ∷ a₁ ∷ b₁)
  c₂ : Id C ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂) c₀ c₁

-- Testing normalization of ap-top (normalize these with C-c C-n).
egA-A = ap {Δ = ε ▸ A′} (λ w → top w) ([] ∷ a₀ ∷ a₁ ∷ a₂)
egAB-A = ap {Δ = ε ▸ A′ ▸ B} (λ w → top (pop w)) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂)
egABC-A = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top (pop (pop w))) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂ ∷ c₀ ∷ c₁ ∷ c₂)
egAB-B = ap {Δ = ε ▸ A′ ▸ B} (λ w → top w) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂)
egABC-B = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top (pop w)) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂ ∷ c₀ ∷ c₁ ∷ c₂)
egABC-C = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top w) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂ ∷ c₀ ∷ c₁ ∷ c₂)
