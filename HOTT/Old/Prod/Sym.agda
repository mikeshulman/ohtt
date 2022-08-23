{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Prod.Sym where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Sym.Base
open import HOTT.Prod.Base

postulate
  sym× : {Δ : Tel} (A B : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀) × B (δ ₀₀)} {a₀₁ : A (δ ₀₁) × B (δ ₀₁)}
    (a₀₂ : Id (Λ x ⇨ A x × B x) (δ ₀₂) a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀) × B (δ ₁₀)} {a₁₁ : A (δ ₁₁) × B (δ ₁₁)}
    (a₁₂ : Id (Λ x ⇨ A x × B x) (δ ₁₂) a₁₀ a₁₁)
    (a₂₀ : Id (Λ x ⇨ A x × B x) (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id (Λ x ⇨ A x × B x) (δ ₂₁) a₀₁ a₁₁)
    (a₂₂ : Sq (Λ x ⇨ A x × B x) δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁) →
    sym (Λ x ⇨ A x × B x) δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ a₂₂ ≡
    -- This just needs a Sq-AP lemma
    {!(sym (Λ⇨ A) δ {fst a₀₀} {fst a₀₁} (fst a₀₂) {fst a₁₀} {fst a₁₁} (fst a₁₂) (fst a₂₀) (fst a₂₁) {!fst a₂₂!} ,
      sym (Λ⇨ B) δ {snd a₀₀} {snd a₀₁} (snd a₀₂) {snd a₁₀} {snd a₁₁} (snd a₁₂) (snd a₂₀) (snd a₂₁) {!snd a₂₂!})!}

-- TODO: The version with ϕ.

