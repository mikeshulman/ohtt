{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Square.Equality where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base

--------------------------------------------------
-- Congruence for squares and their elements
--------------------------------------------------

Sq≡ : {Δ : Tel} (A : el Δ → Type)
     {δ δ' : el (SQ Δ)} (e : δ ≡ δ')
     {a₀₀ : A (δ ₀₀)} {a₀₀' : A (δ' ₀₀)} (e₀₀ : a₀₀ ≡ʰ a₀₀')
     {a₀₁ : A (δ ₀₁)} {a₀₁' : A (δ' ₀₁)} (e₀₁ : a₀₁ ≡ʰ a₀₁')
     {a₀₂ : Id′₀₂ A δ a₀₀ a₀₁} {a₀₂' : Id′₀₂ A δ' a₀₀' a₀₁'} (e₀₂ : a₀₂ ≡ʰ a₀₂')
     {a₁₀ : A (δ ₁₀)} {a₁₀' : A (δ' ₁₀)} (e₁₀ : a₁₀ ≡ʰ a₁₀')
     {a₁₁ : A (δ ₁₁)} {a₁₁' : A (δ' ₁₁)} (e₁₁ : a₁₁ ≡ʰ a₁₁')
     {a₁₂ : Id′₁₂ A δ a₀₂ a₁₀ a₁₁} {a₁₂' : Id′₁₂ A δ' a₀₂' a₁₀' a₁₁'} (e₁₂ : a₁₂ ≡ʰ a₁₂')
     {a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀} {a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀'} (e₂₀ : a₂₀ ≡ʰ a₂₀')
     {a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁} {a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁'} (e₂₁ : a₂₁ ≡ʰ a₂₁') →
  Sq A δ a₀₂ a₁₂ a₂₀ a₂₁ ≡ Sq A δ' a₀₂' a₁₂' a₂₀' a₂₁'
Sq≡ A reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ = reflᵉ

{-

sq₁₂≡ : {Δ : Tel} (A : el Δ → Type) {δ δ' : el (SQ Δ)} (ϕ : δ ≡ δ')
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} {a₀₂ : Id′₀₂ A δ a₀₀ a₀₁}
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} {a₁₂ : Id′₁₂ A δ a₀₂ a₁₀ a₁₁}
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} {a₀₂' : Id′₀₂ A δ' a₀₀' a₀₁'}
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} {a₁₂' : Id′₁₂ A δ' a₀₂' a₁₀' a₁₁'}
    (e₀₀ : a₀₀ ≡ʰ a₀₀') (e₀₁ : a₀₁ ≡ʰ a₀₁') (e₀₂ : a₀₂ ≡ʰ a₀₂')
    (e₁₀ : a₁₀ ≡ʰ a₁₀') (e₁₁ : a₁₁ ≡ʰ a₁₁') (e₁₂ : a₁₂ ≡ʰ a₁₂')
  → _≡_
    {el (ID (ID Δ)
     ▸ (λ x → A (x ₀₀))
     ▸ (λ x → A (pop x ₀₁))
     ▸ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
     ▸ (λ x → A (pop (x ₀) ₁))
     ▸ (λ x → A (pop (pop x ₁) ₁))
     ▸ (λ x → Id′ (λ y → A (pop y ₁)) (pop (pop x)) (top (pop x)) (top x)))}
    (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂)
    (δ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ a₁₂')
sq₁₂≡ A reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ = reflᵉ

sq₂₂≡ : {Δ : Tel} (A : el Δ → Type) {δ δ' : el (SQ Δ)} (ϕ : δ ≡ δ')
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} {a₀₂ : Id′₀₂ A δ a₀₀ a₀₁}
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} {a₁₂ : Id′₁₂ A δ a₀₂ a₁₀ a₁₁}
    {a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀} {a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁}
    {a₂₂ : Id′ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂) a₂₀ a₂₁}
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} {a₀₂' : Id′₀₂ A δ' a₀₀' a₀₁'}
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} {a₁₂' : Id′₁₂ A δ' a₀₂' a₁₀' a₁₁'}
    {a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀'} {a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁'}
    {a₂₂' : Id′ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (δ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ a₁₂') a₂₀' a₂₁'}
    (e₀₀ : a₀₀ ≡ʰ a₀₀') (e₀₁ : a₀₁ ≡ʰ a₀₁') (e₀₂ : a₀₂ ≡ʰ a₀₂')
    (e₁₀ : a₁₀ ≡ʰ a₁₀') (e₁₁ : a₁₁ ≡ʰ a₁₁') (e₁₂ : a₁₂ ≡ʰ a₁₂')
    (e₂₀ : a₂₀ ≡ʰ a₂₀') (e₂₁ : a₂₁ ≡ʰ a₂₁') (e₂₂ : a₂₂ ≡ʰ a₂₂')
  → _≡_
    {el (ID (ID Δ)
     ▸ (λ x → A (x ₀₀))
     ▸ (λ x → A (pop x ₀₁))
     ▸ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
     ▸ (λ x → A (pop (x ₀) ₁))
     ▸ (λ x → A (pop (pop x ₁) ₁))
     ▸ (λ x → Id′ (λ y → A (pop y ₁)) (pop (pop x)) (top (pop x)) (top x))
     ▸ (λ x → Id′ A (pop (pop (x ₀))) (top (pop (x ₀))) (top (x ₀)))
     ▸ (λ x → Id′ A (pop (pop (pop x ₁))) (top (pop (pop x ₁))) (top (pop x ₁)))
     ▸ (λ x → Id′ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) (pop (pop x)) (top (pop x)) (top x)))}
    (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂)
    (δ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ a₁₂' ∷ a₂₀' ∷ a₂₁' ∷ a₂₂')
sq₂₂≡ A reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ = reflᵉ

--------------------
-- Blips
--------------------

blip : {Δ : Tel} (δ : el (SQ Δ))
  (β₀₂ : el (ID Δ)) (e₀₂ : β₀₂ ≡ δ ₀₂)
  (β₁₂ : el (ID Δ)) (e₁₂ : β₁₂ ≡ δ ₁₂)
  (β₂₀ : el (ID Δ)) (e₂₀ : β₂₀ ≡ δ ₂₀)
  (β₂₁ : el (ID Δ)) (e₂₁ : β₂₁ ≡ δ ₂₁)
  → el (SQ Δ)
blip δ _ reflᵉ _  reflᵉ _ reflᵉ _ reflᵉ = δ

blip≡ : {Δ : Tel} (δ : el (SQ Δ))
  (β₀₂ : el (ID Δ)) (e₀₂ : β₀₂ ≡ δ ₀₂)
  (β₁₂ : el (ID Δ)) (e₁₂ : β₁₂ ≡ δ ₁₂)
  (β₂₀ : el (ID Δ)) (e₂₀ : β₂₀ ≡ δ ₂₀)
  (β₂₁ : el (ID Δ)) (e₂₁ : β₂₁ ≡ δ ₂₁)
  → δ ≡ blip δ β₀₂ e₀₂ β₁₂ e₁₂ β₂₀ e₂₀ β₂₁ e₂₁
blip≡ δ _ reflᵉ _  reflᵉ _ reflᵉ _ reflᵉ = reflᵉ

-}
