{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Square.Degenerate

------------------------------
-- Transport
------------------------------

postulate
  tr→ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀)) → A (δ ₁)
  lift→ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀)) → Id′ A δ a₀ (tr→ A δ a₀)
  tr← : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : A (δ ₁)) → A (δ ₀)
  lift← : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : A (δ ₁)) → Id′ A δ (tr← A δ a₁) a₁
  utr→ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀))
    (a₁ a₁' : A (δ ₁)) (a₂ : Id′ A δ a₀ a₁) (a₂' : Id′ A δ a₀ a₁') → Id (A (δ ₁)) a₁ a₁'
  ulift→ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀))
    (a₁ a₁' : A (δ ₁)) (a₂ : Id′ A δ a₀ a₁) (a₂' : Id′ A δ a₀ a₁') →
    Id′ {ε ▸ (λ _ → A (δ ₁))} (λ w → Id′ A δ a₀ (top w)) ([] ∷ a₁ ∷ a₁' ∷ utr→ A δ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  utr← : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : A (δ ₁))
    (a₀ a₀' : A (δ ₀)) (a₂ : Id′ A δ a₀ a₁) (a₂' : Id′ A δ a₀' a₁) → Id (A (δ ₀)) a₀ a₀'
  ulift← : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : A (δ ₁))
    (a₀ a₀' : A (δ ₀)) (a₂ : Id′ A δ a₀ a₁) (a₂' : Id′ A δ a₀' a₁) →
    Id′ {ε ▸ (λ _ → A (δ ₀))} (λ w → Id′ A δ (top w) a₁) ([] ∷ a₀ ∷ a₀' ∷ utr← A δ a₁ a₀ a₀' a₂ a₂') a₂ a₂'

-- Do we need to assert that these are preserved by the functoriality
-- equalities for Id′?

-- The "2-simplex" produced by ulift can be regarded as a square.

ulift→sq : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀))
    (a₁ a₁' : A (δ ₁)) (a₂ : Id′ A δ a₀ a₁) (a₂' : Id′ A δ a₀ a₁') →
    Sq A (DEGSQ-LR δ)
      (refl a₀) (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) (DEGSQ-LR δ) (refl a₀) (utr→ A δ a₀ a₁ a₁' a₂ a₂'))
      a₂ a₂'
ulift→sq {Δ} A δ a₀ a₁ a₁' a₂ a₂' =
  coe← (Id′-AP {ε ▸ (λ _ → A (δ ₁))} {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A (pop x ₁))} (λ x → δ ∷ a₀ ∷ top x)
                 ([] ∷ a₁ ∷ a₁' ∷ utr→ A δ a₀ a₁ a₁' a₂ a₂') (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) a₂ a₂')
        (ulift→ A δ a₀ a₁ a₁' a₂ a₂')

ulift←sq : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : A (δ ₁))
    (a₀ a₀' : A (δ ₀)) (a₂ : Id′ A δ a₀ a₁) (a₂' : Id′ A δ a₀' a₁) →
    Sq A (DEGSQ-LR δ)
      (utr← A δ a₁ a₀ a₀' a₂ a₂') (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) (DEGSQ-LR δ) (utr← A δ a₁ a₀ a₀' a₂ a₂') (refl a₁))
      a₂ a₂'
ulift←sq {Δ} A δ a₁ a₀ a₀' a₂ a₂' =
  coe← (Id′-AP {ε ▸ (λ _ → A (δ ₀))} {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A (pop x ₁))} (λ x → δ ∷ top x ∷ a₁)
                 ([] ∷ a₀ ∷ a₀' ∷ utr← A δ a₁ a₀ a₀' a₂ a₂') (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) a₂ a₂')
        (ulift← A δ a₁ a₀ a₀' a₂ a₂')
