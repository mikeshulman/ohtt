{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --experimental-lossy-unification #-}

module HOTT.Universe.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Fill
open import HOTT.Sigma
open import HOTT.Pi
open import HOTT.Copy
open import HOTT.Groupoids
open import HOTT.Universe.Base

postulate
  tr→Type : {Δ : Tel} (δ : el (ID Δ)) (a₀ : Type) → tr→ {Δ} (Λ _ ⇨ Type) δ a₀ ≡ a₀
  tr←Type : {Δ : Tel} (δ : el (ID Δ)) (a₁ : Type) → tr← {Δ} (Λ _ ⇨ Type) δ a₁ ≡ a₁

{-# REWRITE tr→Type tr←Type #-}

postulate
  lift→Type : {Δ : Tel} (δ : el (ID Δ)) (a₀ : Type) → lift→ {Δ} (Λ _ ⇨ Type) δ a₀ ≡ refl a₀
  lift←Type : {Δ : Tel} (δ : el (ID Δ)) (a₁ : Type) → lift← {Δ} (Λ _ ⇨ Type) δ a₁ ≡ refl a₁

{-# REWRITE lift→Type lift←Type #-}

postulate
  utr→Type : {Δ : Tel} (δ : el (ID Δ)) (a₀ : Type)
    (a₁ a₁' : Type) (a₂ : Id {Δ} (Λ _ ⇨ Type) δ a₀ a₁) (a₂' : Id {Δ} (Λ _ ⇨ Type) δ a₀ a₁') →
    utr→      {Δ} (Λ _ ⇨ Type) δ a₀ a₁ a₁' a₂ a₂' ≡
    fill-utr→ {Δ} (Λ _ ⇨ Type) δ a₀ a₁ a₁' a₂ a₂'
  utr←Type : {Δ : Tel} (δ : el (ID Δ)) (a₁ : Type)
    (a₀ a₀' : Type) (a₂ : Id {Δ} (Λ _ ⇨ Type) δ a₀ a₁) (a₂' : Id {Δ} (Λ _ ⇨ Type) δ a₀' a₁) →
         utr← {Δ} (Λ _ ⇨ Type) δ a₁ a₀ a₀' a₂ a₂' ≡
    fill-utr← {Δ} (Λ _ ⇨ Type) δ a₁ a₀ a₀' a₂ a₂'

{-# REWRITE utr→Type utr←Type #-}

postulate
  ulift→Type : {Δ : Tel} (δ : el (ID Δ)) (a₀ : Type)
    (a₁ a₁' : Type) (a₂ : Id {Δ} (Λ _ ⇨ Type) δ a₀ a₁) (a₂' : Id {Δ} (Λ _ ⇨ Type) δ a₀ a₁') →
         ulift→ {Δ} (Λ _ ⇨ Type) δ a₀ a₁ a₁' a₂ a₂' ≡
    fill-ulift→ {Δ} (Λ _ ⇨ Type) δ a₀ a₁ a₁' a₂ a₂'
  ulift←Type : {Δ : Tel} (δ : el (ID Δ)) (a₁ : Type)
    (a₀ a₀' : Type) (a₂ : Id {Δ} (Λ _ ⇨ Type) δ a₀ a₁) (a₂' : Id {Δ} (Λ _ ⇨ Type) δ a₀' a₁) →
         ulift← {Δ} (Λ _ ⇨ Type) δ a₁ a₀ a₀' a₂ a₂' ≡
    fill-ulift← {Δ} (Λ _ ⇨ Type) δ a₁ a₀ a₀' a₂ a₂'

{-# REWRITE ulift→Type ulift←Type #-}
