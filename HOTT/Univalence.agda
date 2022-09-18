module HOTT.Univalence where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube
open import HOTT.Universe
open import HOTT.Functoriality
open import HOTT.Sigma5
open import HOTT.Square.Simple
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
-- Univalence
------------------------------

-- We need to compute ap's (and refls) of concrete things into the
-- universe (type formers and ua) into some primitive higher version
-- of themselves, analogously to how ap-kan computes to a higher kan.
-- Then the higher kan's can compute on those.  This is an analogue of
-- the "bury" of √-types, applied directly to the universe.

postulate
  -- Eventually we want this to only apply to successor exo-naturals,
  -- since we don't want to be constructing arbitrary new *types* in
  -- the universe without saying what their elements are.  However,
  -- making it literally a successor is too much for Agda, as it then
  -- tries to evaluate everything one step further.  So, for now,
  -- we're letting "𝐬n" be an arbitrary exo-natural.  Eventually we
  -- could e.g. make this bit private in a module and only export its
  -- instance for successors.
  ua : {𝐬n : ℕᵉ} {Γ : Type} (A : Γ → ∂ (𝐬n) Type)
    (k : (x : Γ) → Kan (𝐬n) ∙ A x)
    -- Missing assumption
    (x : Γ) → Cube (𝐬n) Type ∙ A x
  kan-ua : {𝐬n : ℕᵉ} {Γ : Type} (A : Γ → ∂ (𝐬n) Type)
    (k : (x : Γ) → Kan (𝐬n) ∙ A x) →
    (x : Γ) → kan (A x , ua A k x) ≡ k x
{-# REWRITE kan-ua #-}

frob-ap-ua : {𝐬n : ℕᵉ} {Γ : Type} (A : Γ ⇒ ∂ (𝐬n) Type)
  (k : (x : Γ) → Kan (𝐬n) ∙ (A ∙ x))
  {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (y : Δ → Γ) →
  snd (kan (★ ⸴ ★ ⸴ ★ ⸴ Cube 𝐬n Type ∙ (A ∙ y δ₀) ⸴ Cube 𝐬n Type ∙ (A ∙ y δ₁) ,
           refl (Cube 𝐬n Type) ∙ (A ∙ y δ₀ , A ∙ y δ₁ , ap (λ z → A ∙ y z) δ₂)))
      ／ ua (A ∙_) k (y δ₀) ～ ua (A ∙_) k (y δ₁)
frob-ap-ua {𝐬n} {Γ} A k {Δ} {δ₀} {δ₁} δ₂ y =
  ua {𝐬 𝐬n} {ID Γ}
      (λ x → A ∙ ₁st x ⸴ A ∙ ₂nd x ⸴ ap (A ∙_) (₃rd' x) ⸴ ua (A ∙_) k (₁st x) ⸴ ua (A ∙_) k (₂nd x))
      -- TODO: This requires ap-functoriality of Kan.  We should make
      -- (Kan n) into a ⇒ type so that that happens automatically.
      -- But doing so leads to a de Bruijn error in
      -- Functoriality.agda.
      (λ x → {!ap k (ap y δ₂)!} ,
      -- This goal will tell us the type of the missing assumption in
      -- ua.  (Of course, when we add that, we then have to lift it to
      -- the next level call as well.)
             {!!})
      (y δ₀ , y δ₁ , ap y δ₂)

postulate
  ap-ua : {𝐬n : ℕᵉ} {Γ : Type} (A : Γ → ∂ (𝐬n) Type)
    (k : (x : Γ) → Kan (𝐬n) ∙ A x)
    {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (y : Δ → Γ) →
    ap {Δ} {λ δ → Cube (𝐬n) Type ∙ A (y δ)} (λ δ → ua A k (y δ)) {δ₀} {δ₁} δ₂ ≡
    frob-ap-ua (𝛌 A) k δ₂ y
-- {-# REWRITE ap-ua #-}
