module HOTT.Exonat where

open import HOTT.Base

data ℕᵉ : Typeᵉ where
  𝐳 : ℕᵉ
  𝐬 : ℕᵉ → ℕᵉ

data Finᵉ : ℕᵉ → Typeᵉ where
  𝐳 : {n : ℕᵉ} → Finᵉ (𝐬 n)
  𝐬 : {n : ℕᵉ} → Finᵉ n → Finᵉ (𝐬 n)
