{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --cumulativity #-}

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
  tr→ : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₀ : A ⊘ (δ ₀)) → A ⊘ (δ ₁)
  lift→ : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₀ : A ⊘ (δ ₀)) → Id A δ a₀ (tr→ A δ a₀)
  tr← : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₁ : A ⊘ (δ ₁)) → A ⊘ (δ ₀)
  lift← : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₁ : A ⊘ (δ ₁)) → Id A δ (tr← A δ a₁) a₁
  utr→ : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₀ : A ⊘ (δ ₀))
    (a₁ a₁' : A ⊘ (δ ₁)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀ a₁') → (a₁ ＝ a₁')
  ulift→ : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₀ : A ⊘ (δ ₀))
    (a₁ a₁' : A ⊘ (δ ₁)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀ a₁') →
    Id {ε ▸ (Λ _ ⇨ A ⊘ (δ ₁))} (Λ w ⇨ Id A δ a₀ (top w))
      ([] ∷ a₁ ∷ a₁' ∷ utr→ A δ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  utr← : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₁ : A ⊘ (δ ₁))
    (a₀ a₀' : A ⊘ (δ ₀)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀' a₁) → (a₀ ＝ a₀')
  ulift← : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₁ : A ⊘ (δ ₁))
    (a₀ a₀' : A ⊘ (δ ₀)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀' a₁) →
    Id {ε ▸ (Λ _ ⇨ A ⊘ (δ ₀))} (Λ w ⇨ Id A δ (top w) a₁)
      ([] ∷ a₀ ∷ a₀' ∷ utr← A δ a₁ a₀ a₀' a₂ a₂') a₂ a₂'

-- Do we need to assert that these are preserved by the functoriality
-- equalities for Id?  They should be automatically for concrete
-- types, and maybe we don't need the abstract version for anything.
