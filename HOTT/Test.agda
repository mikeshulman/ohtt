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
-- Observe that the results involve coercions along Id-pop, but we can
-- hope that for concrete types these will compute away.  In
-- particular, with Id-pop-const, the coercions already vanish for the
-- "-A" versions.
egA-A = ap {Δ = ε ▸ A′} (λ w → top w) ([] ∷ a₂)
egAB-B = ap {Δ = ε ▸ A′ ▸ B} (λ w → top w) ([] ∷ a₂ ∷ b₂)
egAB-A = ap {Δ = ε ▸ A′ ▸ B} (λ w → top (pop w)) ([] ∷ a₂ ∷ b₂)
egABC-C = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top w) ([] ∷ a₂ ∷ b₂ ∷ c₂)
egABC-B = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top (pop w)) ([] ∷ a₂ ∷ b₂ ∷ c₂)
egABC-A = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top (pop (pop w))) ([] ∷ a₂ ∷ b₂ ∷ c₂)
