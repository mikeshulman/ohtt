{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Sqrt where

open import HOTT.Base
open import HOTT.Id
-- The definition of √ is in the Universe file, since it requires Id
-- and is required for the universe.
open import HOTT.Universe public
open import HOTT.Square

------------------------------
-- Computation in √
------------------------------

postulate
  dig-ap-bury : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type} {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂))
    (@♭ k₀ k₁ : K) (@♭ k₂ : k₀ ＝ k₁) →
    dig {I} {A} {j k₀} {j k₁} {ap j k₂} {bury A j d k₀} {bury A j d k₁} (ap (bury A j d) k₂) ≡ d k₀ k₁ k₂
  dig-refl-bury : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {@♭ K : Type} (@♭ j : K → I) (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂)) (@♭ k : K) →
    dig {I} {A} {j k} {j k} {refl (j k)} {bury A j d k} {bury A j d k} (refl (bury A j d k)) ≡ d k k (refl k)
{-# REWRITE dig-ap-bury dig-refl-bury #-}

------------------------------
-- Identifications in √
------------------------------

-- TODO: This should be a computation of (refl (√ A)).  Actually it
-- *should* really be (ap (√ A)), but since we defined (√ A) to take
-- its argument with ∙ (which makes things compute better in other
-- places) we need to use refl instead.
postulate
  Id-√ : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {i₀ i₁ : I} {i₂ : i₀ ＝ i₁} (s₀ : √ A ∙ i₀) (s₁ : √ A ∙ i₁) →
    -- Id (√ A ∙_) i₂ s₀ s₁ ≡
    (dig (ap kan (refl (√ A) ∙ (i₀ , i₁ , i₂)))) ／ s₀ ～ s₁ ≡
    A i₀ i₁ i₂ ×
    √ {（ i₀ ⦂ I ）× （ i₁ ⦂ I ）× （ i₂ ⦂ i₀ ＝ i₁ ）× √ A ∙ i₀ × √ A ∙ i₁}
      (λ u₀ u₁ u₂ → Id {ID I} (λ iₓ → A (₁st iₓ) (₂nd iₓ) (₃rd' iₓ))
                       {₁st u₀ , ₁st u₁ , ₁st u₂}
                       {₂nd u₀ , ₂nd u₁ , ₂nd u₂}
                       (₃rd u₀ , ₃rd u₁ , sym I (₁st u₂) (₂nd u₂) (₃rd u₀) (₃rd u₁) (₃rd u₂) )
                       (dig {I} {A} {₁st u₀} {₁st u₁} {₁st u₂} {₄th u₀} {₄th u₁} (₄th u₂) )
                       (dig {I} {A} {₂nd u₀} {₂nd u₁} {₂nd u₂} {₅th' u₀} {₅th' u₁} (₅th' u₂))) ∙
      (i₀ , i₁ , i₂ , s₀ , s₁)
{-# REWRITE Id-√ #-}

{-
postulate
  dig-def : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {i₀ i₁ : I} (i₂ : i₀ ＝ i₁) {s₀ : √ A ∙ i₀} {s₁ : √ A ∙ i₁} (s₂ : Id (√ A ∙_) i₂ s₀ s₁) →
    {!dig {I} {A} {i₀} {i₁} {i₂} {s₀} {s₁} s₂ ≡ fst s₂!}
-}
--{-# REWRITE dig-def #-}

