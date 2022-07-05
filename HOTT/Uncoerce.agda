{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Uncoerce where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id


-- Since Id-AP⊚ always fires as a rewrite, we don't need to coerce
-- along it by hand.  But sometimes we do need to coerce along Id-AP
-- by hand, since the LHS ⊘ can be reduced and unmatchable.  However,
-- if we declare it to reduce to reflᵉ, then such coercions will
-- disappear, as we expect them to do in concrete cases where Id-AP
-- should hold by definition anyway.

Id-AP-reflᵉ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (A : Δ ⇨ Type)
  (a₀ : A ⊘ (f (γ ₀))) (a₁ : A ⊘ (f (γ ₁))) →
  Id-AP f γ A a₀ a₁ ≡ᵉ reflᵉ
Id-AP-reflᵉ f γ A a₀ a₁ = axiomK

{-# REWRITE Id-AP-reflᵉ #-}

-- As with Id-AP, we declare AP-AP to reduce to reflᵉᵉ so that it
-- disappears on concrete terms like it should.
AP-AP-reflᵉ : {Γ Δ Θ : Tel} (f : Γ ⇨ᵉ el Δ) (g : Δ ⇨ᵉ el Θ) (γ : el (ID Γ)) →
  AP-AP f g γ ≡ᵉ reflᵉᵉ
AP-AP-reflᵉ f g γ = axiomKᵉ

{-# REWRITE AP-AP-reflᵉ #-}

-- We put these rewrites in a separate file since during development
-- of the general theory, they can create impossible situations, so we
-- may want to avoid importing them.

