{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Univalence where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Universe
open import HOTT.Square.Heterogeneous.Base

infix 40 _↑

------------------------------------------
-- One-to-one correspondences
----------------------------------------

isProp : (A : Type) → Type
isProp A = （ a₀ ⦂ A ）⇒ （ a₁ ⦂ A ）⇒ (a₀ ＝ a₁)

isContr : (A : Type) → Type
isContr A = A × isProp A

_≃_ : (A B : Type) → Type
A ≃ B = （ rel ⦂ A ⇒ B ⇒ Type ）×
        (（ a ⦂ A ）⇒ isContr (（ b ⦂ B ）× rel ∙ a ∙ b)) ×
        (（ b ⦂ B ）⇒ isContr (（ a ⦂ A ）× rel ∙ a ∙ b))

------------------------------
-- Computing kan
------------------------------

{-
postulate
  kan′ : {n : ℕᵉ} (A : SqU n) {Ω : Type} ⦃ ω : Kan n A ≡ Ω ⦄ → Ω

frob-kan-ap : {n : ℕᵉ} {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (A : Δ → SqU n)
  {Ω : Type} (ω : Kan (𝐬 n) (A δ₀ , A δ₁ , ap A δ₂) ≡ Ω) → Ω
frob-kan-ap {n} δ₂ A reflᵉ = {!ap (λ δ → kan′ {n} (A δ) ⦃ reflᵉ ⦄) δ₂!} , {!!}

postulate
  kan-ap : {n : ℕᵉ} {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (A : Δ → SqU n)
    {Ω : Type} {ω : Kan (𝐬 n) (A δ₀ , A δ₁ , ap A δ₂) ≡ Ω} →
    kan {𝐬 n} (A δ₀ , A δ₁ , ap A δ₂) ⦃ ω ⦄ ≡ frob-kan-ap δ₂ A ω
-}
-- That idea seems to be going nowhere, since kan′ isn't
-- definitionally equal to kan and so we can't actually reduce kan-ap
-- to an ap-kan′.

------------------------------
-- Univalence
------------------------------

postulate
  _↑ : {A B : Type} → (A ≃ B) → (A ＝ B)
  kan₁-↑ : {A B : Type} (e : A ≃ B) → kan (A , B , e ↑) ≡ ★ ,
    ≊[ ₁st e , (ƛ a ⇒ fst (fst (₂nd e ∙ a))) , (ƛ b ⇒ fst (fst (₃rd' e ∙ b))) ,
               (ƛ a ⇒ snd (fst (₂nd e ∙ a))) , (ƛ b ⇒ snd (fst (₃rd' e ∙ b))) ]
{-# REWRITE kan₁-↑ #-}

postulate
  kan₂-↑ : {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (A B : Δ → Type) (e : (δ : Δ) → A δ ≃ B δ) →
    kan {𝐬 (𝐬 𝐳)} ((A δ₀ , B δ₀ , e δ₀ ↑) , (A δ₁ , B δ₁ , e δ₁ ↑) , (ap A δ₂ , ap B δ₂ ,
      ←Id-ap (λ δ → A δ , B δ) (ƛ x ⇒ fst x ＝ snd x) δ₂ (ap (λ δ → e δ ↑) δ₂))) ⦃ reflᵉ ⦄ ≡
    -- This is what it should be morally, but (aside from needing
    -- functoriality to give it) we can't actually compute it to that,
    -- since it would make a rewrite loop with ap-kan.
    {!ap (λ δ → kan (A δ , B δ , e δ ↑)) δ₂!} ,
    -- This one is the proof of ap-equiv.
    {!!}

-- I think we need to compute ap's (and refls) of concrete things into
-- the universe (type formers and ua) into some primitive higher
-- version of themselves, analogously to how ap-kan computes to a
-- higher kan.  Then the higher kan's can compute on those.  This must
-- be some analogue of "bury" for √-types.

-- I'm not sure how to do this without breaking SqU into a separate
-- boundary and cube type, since the "higher bury" ought to take
-- values in something that depends definitionally on the lower ones,
-- as in this basic example:
postulate
  ap-↑ : {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (A B : Δ → Type) (e : (δ : Δ) → A δ ≃ B δ) →
    ap (λ δ → e δ ↑) δ₂ ≡ {!!}
