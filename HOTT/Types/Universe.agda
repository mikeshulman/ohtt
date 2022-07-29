{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Types.Universe where

open import HOTT.Rewrite
open import HOTT.Identity
open import HOTT.Telescope
open import HOTT.Types.Sigma
open import HOTT.Types.Pi

----------------------------------------
-- Identity types of the universe
----------------------------------------

record _＝U_ (A B : Type) : Type where
  no-eta-equality
  field
    _//_~_ : (a : A) (b : B) → Type
    tr→ : A → B
    lift→ : (a : A) → _//_~_ a (tr→ a)
    tr← : B → A
    lift← : (b : B) → _//_~_ (tr← b) b
    utr→ : (a : A) (b₀ b₁ : B) (r₀ : _//_~_ a b₀) (r₁ : _//_~_ a b₁) → (b₀ , r₀) ＝ (b₁ , r₁)
    utr← : (b : B) (a₀ a₁ : A) (r₀ : _//_~_ a₀ b) (r₁ : _//_~_ a₁ b) → (a₀ , r₀) ＝ (a₁ , r₁)

open _＝U_ public

postulate
  ＝U : (A B : Type) → (A ＝ B) ≡ (A ＝U B)

{-# REWRITE ＝U #-}

postulate
  refl//~ : (A : Type) (a₀ a₁ : A) → (refl A // a₀ ~ a₁) ≡ (a₀ ＝ a₁)

{-# REWRITE refl//~ #-}

----------------------------------------
-- Identity types of eliminators
----------------------------------------

-- Since refl//~ computes to ＝ rather than vice versa, we need to
-- assert the computation rules that would apply to refl also for ＝.
-- Since Type has no introduction forms, this just means eliminators.

-- It seems that this ought to go in Pi2.agda, but when put there it
-- takes forever.
postulate
  ＝∙ : (A : Type) (B : A ⇒ Type) (a : A) (b₀ b₁ : B ∙ a) → (b₀ ＝ b₁) ≡ refl B ∙ a ∙ a ∙ refl a // b₀ ~ b₁

{-# REWRITE ＝∙ #-}

