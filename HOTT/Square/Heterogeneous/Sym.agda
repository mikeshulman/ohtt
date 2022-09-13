{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Square.Heterogeneous.Sym where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube
open import HOTT.Universe.Parametric
open import HOTT.Functoriality
open import HOTT.Square.Simple
open import HOTT.Unit
open import HOTT.IdCube
open import HOTT.Corr
open import HOTT.Square.Heterogeneous.Base
open import HOTT.Square.Heterogeneous.Flip

∂2→∂ : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁) →
  ∂ (𝐬 (𝐬 𝐳)) A
∂2→∂ {A} {a₀₀} {a₀₁} {a₁₀} {a₁₁} ┌─ a₁₂ ─┐
                                 a₂₀ □ a₂₁
                                 └─ a₀₂ ─┘ =
  ((★ , ★ , ★ , a₀₀ , a₁₀) , (★ , ★ , ★ , a₀₁ , a₁₁) ,
   ((★ , ★ , ★ , a₀₂ , a₁₂) , (a₂₀ , a₂₁)))

Sq→CUBE : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁) →
  Sq A a → CUBE (𝐬 (𝐬 𝐳)) A
Sq→CUBE {A} {a₀₀} {a₀₁} {a₁₀} {a₁₁} a a₂₂ = (∂2→∂ a , a₂₂)

------------------------------
-- corr on sym
------------------------------

frob-corr-sym : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {Ω : Type} ⦃ ω : Corr (𝐬 (𝐬 𝐳)) ∙ ∂2→∂ (sym-∂2 A) ≡ Ω ⦄ → Ω
frob-corr-sym A A₂₂ ⦃ reflᵉ ⦄ =
  let C = corr (Sq→CUBE A A₂₂) ⦃ reflᵉ ⦄ in
  ((★ , snd C) , snd (fst C))

-- TODO: Sq→CUBE etc. should be reduced in the LHS, to increase the
-- chances of it actually firing.
postulate
  corr-sym : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {Ω : Type} ⦃ ω : Corr (𝐬 (𝐬 𝐳)) ∙ ∂2→∂ (sym-∂2 A) ≡ Ω ⦄ →
    corr {𝐬 (𝐬 𝐳)} (Sq→CUBE (sym-∂2 A) (sym Type A A₂₂)) ⦃ ω ⦄ ≡
    frob-corr-sym A A₂₂ ⦃ ω ⦄
{-# REWRITE corr-sym #-}

-- Since refl-refl is a fixpoint of sym, this entails that the two
-- components of corr on refl-refl are identical.  I think this one
-- can't include a ω because we need to project out the second
-- component.

postulate
  corr-refl-refl : (A : Type) →
    snd (corr {𝐬 (𝐬 𝐳)} (Sq→CUBE (refl-∂2 A) (refl (refl A))) ⦃ reflᵉ ⦄) ≡
    snd (fst (corr {𝐬 (𝐬 𝐳)} (Sq→CUBE (refl-∂2 A) (refl (refl A))) ⦃ reflᵉ ⦄))
  -- We also posit a version in which Sq→CUBE appears in reduced form,
  -- which I think will probably fire more often.
  corr-refl-refl′ : (A : Type) →
    snd (corr {𝐬 (𝐬 𝐳)}
      (((★ , ★ , ★ , A , A) , (★ , ★ , ★ , A , A) , (★ , ★ , ★ , refl A , refl A) ,
        refl A , refl A) , refl (refl A)) ⦃ reflᵉ ⦄) ≡
    (snd (fst (corr {𝐬 (𝐬 𝐳)} (Sq→CUBE (refl-∂2 A) (refl (refl A))) ⦃ reflᵉ ⦄)))
{-# REWRITE corr-refl-refl corr-refl-refl′ #-}

----------------------------------------
-- flip computes on refl to sym.
----------------------------------------

-- Heap size exhausted!
postulate
  flip-refl-refl : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (a : ∂2ʰ (refl-∂2 A) (refl (refl A)) a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sqʰ (refl-∂2 A) (refl (refl A)) a) →
    flip (refl-∂2 A) (refl (refl A)) a a₂₂ ≡ sym A (∂2ʰ-refl-refl a) a₂₂
