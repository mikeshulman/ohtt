{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Corr where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube
open import HOTT.Universe.Parametric
open import HOTT.Functoriality
open import HOTT.Square.Simple
open import HOTT.Unit
open import HOTT.IdCube

------------------------------
-- Computing gCorr on 𝐬
------------------------------

-- Finally, we have all the necessary structure to be able to compute
-- gCorr on successors.

postulate
  gCorr-𝐬-def : (n : ℕᵉ) → gCorr-𝐬 n ≡ ƛ A ⇒
    Id (gCorr n ∙_)
    {A !₀ !₀ , A !₁ !₀ , ‼₀ (A !₀) (A !₁) (A !₂) , A !₀ !⁰ , A !₁ !⁰}
    {A !₀ !₁ , A !₁ !₁ , ‼₁ (A !₀) (A !₁) (A !₂) , A !₀ !¹ , A !₁ !¹}
    (A !₀ !₂ , A !₁ !₂ ,
    sym (∂ n Type) ┌─  ‼₁ (A !₀) (A !₁) (A !₂)  ─┐
                   A !₀ !₂        □        A !₁ !₂
                   └─  ‼₀ (A !₀) (A !₁) (A !₂)  ─┘ (‼₂ (A !₀) (A !₁) (A !₂)) ,
    A !⁰ , A !¹)
    (snd (corr {𝐬 n} ((A !₀ !₀ , A !₁ !₀ , ‼₀ (A !₀) (A !₁) (A !₂) , A !₀ !⁰ , A !₁ !⁰) , ‼⁰ (A !₀) (A !₁) (A !₂))))
    (snd (corr {𝐬 n} ((A !₀ !₁ , A !₁ !₁ , ‼₁ (A !₀) (A !₁) (A !₂) , A !₀ !¹ , A !₁ !¹) , ‼¹ (A !₀) (A !₁) (A !₂))))
{-# REWRITE gCorr-𝐬-def #-}

------------------------------
-- Reflexivity cubes
------------------------------

-- The definition of REFL on 𝐬 typechecks much faster if the input
-- cube is broken into components (rather than the components being
-- accessed with fst and snd).  But if we actually pattern-match in
-- its definition, then other things later don't typecheck, probably
-- because ap doesn't compute on arbitrary pattern-matched functions.
-- Thus, we use a trick of defining the 𝐬 case separately in a lemma.

REFL : (n : ℕᵉ) (A : Type) → CUBE n A → CUBE (𝐬 n) A
REFL 𝐳 A a = (★ , ★ , ★ , snd a , snd a) , refl (snd a)
REFL (𝐬 n) A a = REFL-𝐬 (fst a) (snd a)
  where REFL-𝐬 : (∂a : ∂ (𝐬 n) A) (a₂ : Cube (𝐬 n) A ∙ ∂a) → CUBE (𝐬 (𝐬 n)) A
        REFL-𝐬 ∂a a₂ = ((∂a , ∂a , refl ∂a , a₂ , a₂) , refl a₂)

-- These would to be provable if we had definitional η-laws for
-- Σ-types.
postulate
  fst-REFL-!₀ : (n : ℕᵉ) (A : Type) (a : CUBE n A) →
    fst (REFL n A a) !₀ ≡ fst a
  fst-REFL-!₁ : (n : ℕᵉ) (A : Type) (a : CUBE n A) →
    fst (REFL n A a) !₁ ≡ fst a
{-# REWRITE fst-REFL-!₀ fst-REFL-!₁ #-}

postulate
  fst-REFL-!₂ : (n : ℕᵉ) (A : Type) (a : CUBE n A) →
    fst (REFL n A a) !₂ ≡ fst (refl a)
  fst-REFL-!⁰ : (n : ℕᵉ) (A : Type) (a : CUBE n A) →
    fst (REFL n A a) !⁰ ≡ snd a
  fst-REFL-!¹ : (n : ℕᵉ) (A : Type) (a : CUBE n A) →
    fst (REFL n A a) !¹ ≡ snd a
{-# REWRITE fst-REFL-!₂ fst-REFL-!⁰ fst-REFL-!¹ #-}

------------------------------
-- refl-corr
------------------------------

-- Finally, we can define refl on corr.  In addition to requiring
-- everything above, this has to be stated (like ap-corr) with a
-- general exo-equality to avoid green slime, so we use an auxiliary
-- lemma to destruct that exo-equality.

frob-refl-corr : {n : ℕᵉ} (A : CUBE n Type) {Ω : Type} ⦃ ω : Corr n ∙ fst A ≡ Ω ⦄ →
  ⟦ refl Ω ⟧ ∙ corr A ∙ corr A
frob-refl-corr {n} A ⦃ ω = reflᵉ ⦄ =
  coeʰ-Id (Corr n ∙_) reflᵉ reflᵉ reflʰ
    (cong (λ e → corr e ⦃ reflᵉ ⦄) (ηΣ (Cube n Type ∙_) A))
    (cong (λ e → corr e ⦃ reflᵉ ⦄) (ηΣ (Cube n Type ∙_) A))
    (fst (corr {𝐬 n} (REFL n Type A) ⦃ reflᵉ ⦄))

postulate
  refl-corr : {n : ℕᵉ} (A : CUBE n Type) {Ω : Type} ⦃ ω : Corr n ∙ fst A ≡ Ω ⦄ →
     refl (corr {n} A ⦃ ω ⦄) ≡ frob-refl-corr A ⦃ ω ⦄
{-# REWRITE refl-corr #-}
