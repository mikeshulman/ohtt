{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Sqrt where

open import HOTT.Base
open import HOTT.Id
-- The definition of √ is in the Universe file, since it requires Id
-- and is required for the universe.
open import HOTT.Universe public
open import HOTT.Square

------------------------------
-- Identifications in √
------------------------------

√′-I : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type) → Type
√′-I {I} A = （ i₀ ⦂ I ）× （ i₁ ⦂ I ）× （ i₂ ⦂ i₀ ＝ i₁ ）× √ A i₀ × √ A i₁

√′-A : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type) →
  (u₀ u₁ : √′-I A) (u₂ : u₀ ＝ u₁) → Type
√′-A {I} A u₀ u₁ u₂ =
  Id {ID I} (λ iₓ → A (₁st iₓ) (₂nd iₓ) (₃rd' iₓ))
    {₁st u₀ , ₁st u₁ , ₁st u₂} {₂nd u₀ , ₂nd u₁ , ₂nd u₂}
    -- NB: There is a symmetry here!
    (₃rd u₀ , ₃rd u₁ , sym I ┌─     ₂nd u₂     ─┐
                             ₃rd u₀   □    ₃rd u₁
                             └─     ₁st u₂     ─┘  (₃rd u₂))
    (dig {I} {A} {₁st u₀} {₁st u₁} {₁st u₂} {₄th u₀} {₄th u₁}
         (←Id-ap {（ z ⦂ I × I ）× fst z ＝ snd z} {I} (λ z → fst (fst z)) (𝛌 (√ A))
                 {(₁st u₀ , ₂nd u₀) , ₃rd u₀} {(₁st u₁ , ₂nd u₁) , ₃rd u₁} ((₁st u₂ , ₂nd u₂) , ₃rd u₂)
                 (₄th u₀) (₄th u₁) (₄th u₂)))
    (dig {I} {A} {₂nd u₀} {₂nd u₁} {₂nd u₂} {₅th' u₀} {₅th' u₁}
         (←Id-ap {（ w ⦂ （ z ⦂ I × I ）× fst z ＝ snd z ）× √ A (fst (fst w))} {I} (λ z → snd (fst (fst z))) (𝛌 (√ A))
                 {((₁st u₀ , ₂nd u₀) , ₃rd u₀) , ₄th u₀} {((₁st u₁ , ₂nd u₁) , ₃rd u₁) , ₄th u₁} (((₁st u₂ , ₂nd u₂) , ₃rd u₂) , ₄th u₂)
                 (₅th' u₀) (₅th' u₁) (₅th' u₂)))

postulate
  ＝-√ : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type} (i : I) (s₀ s₁ : √ A i) →
    (s₀ ＝ s₁) ≡
    A i i (refl i) × √ {√′-I A} (√′-A A) (i , i , refl i , s₀ , s₁)
  Id-√ : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {Δ : Type} (i : Δ → I) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (s₀ : √ A (i δ₀)) (s₁ : √ A (i δ₁)) →
    Id (λ δ → √ A (i δ)) δ₂ s₀ s₁ ≡
    A (i δ₀) (i δ₁) (ap i δ₂) × √ {√′-I A} (√′-A A) (i δ₀ , i δ₁ , ap i δ₂ , s₀ , s₁)
{-# REWRITE ＝-√ Id-√ #-}

postulate
  dig-def : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {i₀ i₁ : I} (i₂ : i₀ ＝ i₁) {s₀ : √ A i₀} {s₁ : √ A i₁} (s₂ : Id (√ A) i₂ s₀ s₁) →
    dig {I} {A} {i₀} {i₁} {i₂} {s₀} {s₁} s₂ ≡ fst s₂
{-# REWRITE dig-def #-}

------------------------------
-- Computation in √
------------------------------

postulate
  refl-bury : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂)) (k : K) →
    refl (bury A j d k) ≡ (d k k (refl k) , {!!})
  -- TODO: ap-bury should have an arbitrary Δ.
  ap-bury : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂))
    {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (k : Δ → K) →
    ap (λ δ → bury A j d (k δ)) δ₂ ≡ ({!d (k δ₀) (k δ₁) (ap k δ₂) !} , {!!})
--{-# REWRITE dig-refl-bury dig-ap-bury #-}
