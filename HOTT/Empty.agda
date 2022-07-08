{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Empty where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport

data ⊥ : Type where

postulate
  ＝⊥ : (u v : ⊥) → (u ＝ v) ≡ ⊥

{-# REWRITE ＝⊥ #-}

postulate
  tr→⊥ : {Δ : Tel} (δ : el (ID Δ)) (a₀ : ⊥) → tr→ {Δ} (Λ _ ⇨ ⊥) δ a₀ ≡ a₀
  lift→⊥ : {Δ : Tel} (δ : el (ID Δ)) (a₀ : ⊥) → lift→ {Δ} (Λ _ ⇨ ⊥) δ a₀ ≡ a₀
  tr←⊥ : {Δ : Tel} (δ : el (ID Δ)) (a₁ : ⊥) → tr← {Δ} (Λ _ ⇨ ⊥) δ a₁ ≡ a₁
  lift←⊥ : {Δ : Tel} (δ : el (ID Δ)) (a₁ : ⊥) → lift← {Δ} (Λ _ ⇨ ⊥) δ a₁ ≡ a₁
  utr→⊥ : {Δ : Tel} (δ : el (ID Δ)) (a₀ : ⊥)
    (a₁ a₁' : ⊥) (a₂ : Id {Δ} (Λ _ ⇨ ⊥) δ a₀ a₁) (a₂' : Id {Δ} (Λ _ ⇨ ⊥) δ a₀ a₁') →
    utr→ {Δ} (Λ _ ⇨ ⊥) δ a₀ a₁ a₁' a₂ a₂' ≡ a₀
  ulift→⊥ : {Δ : Tel} (δ : el (ID Δ)) (a₀ : ⊥)
    (a₁ a₁' : ⊥) (a₂ : Id {Δ} (Λ _ ⇨ ⊥) δ a₀ a₁) (a₂' : Id {Δ} (Λ _ ⇨ ⊥) δ a₀ a₁') →
    ulift→ {Δ} (Λ _ ⇨ ⊥) δ a₀ a₁ a₁' a₂ a₂' ≡ a₀
  utr←⊥ : {Δ : Tel} (δ : el (ID Δ)) (a₁ : ⊥)
    (a₀ a₀' : ⊥) (a₂ : Id {Δ} (Λ _ ⇨ ⊥) δ a₀ a₁) (a₂' : Id {Δ} (Λ _ ⇨ ⊥) δ a₀' a₁) →
    utr← {Δ} (Λ _ ⇨ ⊥) δ a₁ a₀ a₀' a₂ a₂' ≡ a₁
  ulift←⊥ : {Δ : Tel} (δ : el (ID Δ)) (a₁ : ⊥)
    (a₀ a₀' : ⊥) (a₂ : Id {Δ} (Λ _ ⇨ ⊥) δ a₀ a₁) (a₂' : Id {Δ} (Λ _ ⇨ ⊥) δ a₀' a₁) →
    ulift← {Δ} (Λ _ ⇨ ⊥) δ a₁ a₀ a₀' a₂ a₂' ≡ a₁

{-# REWRITE tr→⊥ lift→⊥ tr←⊥ lift←⊥ utr→⊥ ulift→⊥ utr←⊥ ulift←⊥ #-}
