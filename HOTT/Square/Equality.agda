{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Square.Equality where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base

sq₁₂≡ : {Δ : Tel} (A : el Δ → Type) {δ δ' : el (SQ Δ)} (ϕ : δ ≡ δ')
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} {a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁}
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} {a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁}
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} {a₀₂' : Id′ A (δ' ₀₂) a₀₀' a₀₁'}
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} {a₁₂' : Id′ A (δ' ₁₂) a₁₀' a₁₁'}
    (e₀₀ : a₀₀ ≡ʰ a₀₀') (e₀₁ : a₀₁ ≡ʰ a₀₁') (e₀₂ : a₀₂ ≡ʰ a₀₂')
    (e₁₀ : a₁₀ ≡ʰ a₁₀') (e₁₁ : a₁₁ ≡ʰ a₁₁') (e₁₂ : a₁₂ ≡ʰ a₁₂')
  → _≡_
    {el (ID (ID Δ)
    ▸ (λ x → A (x ₀₀))
    ▸ (λ x → A ((pop x) ₀₁))
    ▸ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
    ▸ (λ x → A ((pop (pop (pop x))) ₁₀))
    ▸ (λ x → A ((pop (pop (pop (pop x)))) ₁₁))
    ▸ (λ x → Id′ (λ y → A ((pop y) ₁)) (pop (pop x)) (top (pop x)) (top x)))}
    (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
    (δ' ∷ a₀₀' ∷ a₀₁' ∷ frob₀₂ A δ' a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ frob₁₂ A δ' a₀₂' a₁₂')
sq₁₂≡ A reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ = reflᵉ

sq₂₂≡ : {Δ : Tel} (A : el Δ → Type) {δ δ' : el (SQ Δ)} (ϕ : δ ≡ δ')
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} {a₀₂ : Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁}
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} {a₁₂ : Id′ (λ w → A (pop w ₁)) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) a₁₀ a₁₁}
    {a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀} {a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁}
    {a₂₂ : Id′ -- {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A ((pop x) ₁))}
      (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂) a₂₀ a₂₁}
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} {a₀₂' : Id′ (λ x → A (x ₀)) δ' a₀₀' a₀₁'}
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} {a₁₂' : Id′ (λ w → A (pop w ₁)) (δ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂') a₁₀' a₁₁'}
    {a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀'} {a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁'}
    {a₂₂' : Id′ -- {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A ((pop x) ₁))}
      (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (δ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ a₁₂') a₂₀' a₂₁'}
    (e₀₀ : a₀₀ ≡ʰ a₀₀') (e₀₁ : a₀₁ ≡ʰ a₀₁') (e₀₂ : a₀₂ ≡ʰ a₀₂')
    (e₁₀ : a₁₀ ≡ʰ a₁₀') (e₁₁ : a₁₁ ≡ʰ a₁₁') (e₁₂ : a₁₂ ≡ʰ a₁₂')
    (e₂₀ : a₂₀ ≡ʰ a₂₀') (e₂₁ : a₂₁ ≡ʰ a₂₁') (e₂₂ : a₂₂ ≡ʰ a₂₂')
  → _≡_
    {el (ID (ID Δ)
    ▸ (λ x → A (x ₀₀))
    ▸ (λ x → A ((pop x) ₀₁))
    ▸ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
    ▸ (λ x → A ((pop (pop (pop x))) ₁₀))
    ▸ (λ x → A ((pop (pop (pop (pop x)))) ₁₁))
    ▸ (λ x → Id′ (λ y → A ((pop y) ₁)) (pop (pop x)) (top (pop x)) (top x))
    ▸ (λ x → Id′ A (pop (pop (pop (pop (pop (pop x))))) ₀) (top (pop (pop (pop (pop (pop x)))))) (top (pop (pop x))))
    ▸ (λ x → Id′ A (pop (pop (pop (pop (pop (pop (pop x)))))) ₁) (top (pop (pop (pop (pop (pop x)))))) (top (pop (pop x))))
    ▸ (λ x → Id′ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) (pop (pop x)) (top (pop x)) (top x)))}
    (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂)
    (δ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ a₁₂' ∷ a₂₀' ∷ a₂₁' ∷ a₂₂')
sq₂₂≡ A reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ = reflᵉ
