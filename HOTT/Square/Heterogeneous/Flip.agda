module HOTT.Square.Heterogeneous.Flip where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Cube
open import HOTT.Universe.Parametric
open import HOTT.Functoriality
open import HOTT.Square.Simple
open import HOTT.Unit
open import HOTT.IdCube
open import HOTT.Corr
open import HOTT.Square.Heterogeneous.Base

------------------------------
-- Heterogeneous symmetry
------------------------------

-- Morally, unflip should be just flip applied to (sym A₂₂).  But that
-- relies on the computation rule for corr on sym.

postulate
  flip : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) →
    Sqʰ A A₂₂ a → Symʰ A A₂₂ a
  unflip : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) →
    Symʰ A A₂₂ a → Sqʰ A A₂₂ a
postulate
  unflip-flip : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sqʰ A A₂₂ a) →
    unflip A A₂₂ a (flip A A₂₂ a a₂₂) ≡ a₂₂
  flip-unflip : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Symʰ A A₂₂ a) →
    flip A A₂₂ a (unflip A A₂₂ a a₂₂) ≡ a₂₂
{-# REWRITE unflip-flip flip-unflip #-}
