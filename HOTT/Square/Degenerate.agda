{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Square.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square

----------------------------------------
-- Degenerate squares
----------------------------------------

-- Top-bottom degenerate squares in a context
DEGSQ-TB : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → el (SQ Δ δ₂ δ₂ (REFL δ₀) (REFL δ₁))
DEGSQ-TB Δ {δ₀} {δ₁} δ₂ =
  COE← (ID′-AP {Δ} {PROD Δ Δ} (λ w → PR Δ Δ w w) δ₂ (UID Δ) (REFL δ₀) (REFL δ₁))
       (AP′ {Δ} (λ w → ID Δ w w) REFL δ₂)

DEGSQ-LR : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → el (SQ Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂)
DEGSQ-LR Δ {δ₀} {δ₁} δ₂ = COE← (ID′-AP {ε} (λ _ → PR Δ Δ δ₀ δ₁) [] (UID Δ) δ₂ δ₂) (REFL δ₂)

{-
-- Hmm, this should really be for refl of *any* variable in the telescope.
postulate
  ap-refl : {Δ : Tel} {A : el Δ → Type} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) {a₀ : A δ₀} {a₁ : A δ₁} (a₂ : Id′ A δ₂ a₀ a₁) →
    ap {Δ ▸ A} (λ w → refl (top w)) {δ₀ ∷ a₀} {δ₁ ∷ a₁} (δ₂ ∷ a₂) ≡
    {! -- First we need AP-REFL computing to a SYM for telescopes, so
      -- that the type version has something to depend on.

      -- This square telescope:
      --- SQ Δ δ₂ δ₂ (REFL δ₀) (REFL δ₁)
      -- is the type of the third component of
      --- (AP {Δ} {TID Δ} (λ w → tot w w (REFL w)) δ₂)
      -- (The first two components are δ₂; I included them because we don't have a dependent AP for telescopes.)

      -- So we should hope that the goal type can be massaged into:
      --- Sq A δ₂ δ₂ (REFL δ₀) (REFL δ₁) (mid (AP {Δ} {TID Δ} (λ w → tot w w (REFL w)) δ₂)) a₂ a₂ (refl a₀) (refl a₁)
      -- (The last two refls require some munging.)

      -- This square telescope:
      --- SQ Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂
      -- is related to the type of REFL δ₂:
      --- el (ID (ID Δ δ₀ δ₁) δ₂ δ₂)
      -- 

      -- So we should hope to be able to apply symmetry to something like this:
      --- Sq A (REFL δ₀) (REFL δ₁) δ₂ δ₂ ? (refl a₀) (refl a₁) a₂ a₂

   !}
-}
