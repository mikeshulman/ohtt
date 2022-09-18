module HOTT.Universe.Parametric where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube

----------------------------------------
-- Parametric aspects of the universe
----------------------------------------

-- Any identification in the universe gives rise to a correspondence.
-- When combined with ap and sym, this means any cube in the universe
-- gives rise to a "cubical correspondence" over its boundary.  We
-- take these operations on cubes in the universe as normal/neutral,
-- reducing ap and sym to them.

-- The type of "cubical correspondences" over the boundary of a cube
-- in the universe.
Corr : (n : ℕᵉ) → ∂ n Type ⇒ Type

postulate
  -- Here is the function assigning such a cubical correspondence to
  -- each actual cube.  We include an equality to eliminate green
  -- slime in rewrites, notably in ap-corr below which will say that
  -- (ap (corr {n})) is part of (corr {𝐬 n}).  The remaining parts of
  -- (cor {𝐬 n}) are determined by symmetry.
  corr : {n : ℕᵉ} (A : CUBE n Type) {Ω : Type} ⦃ ω : Corr n ∙ fst A ≡ Ω ⦄ → Ω

-- In order to define Corr, recursively on n, we define in parallel a
-- type of "Corr-generators".  It essentially adds one more primitive
-- symmetry every time we go up a dimension.
gCorr : (n : ℕᵉ) → ∂ (𝐬 n) Type ⇒ Type

Corr 𝐳 = ƛ _ ⇒ ⊤
Corr (𝐬 n) = ƛ A ⇒ Id {∂ n Type} (Corr n ∙_) {A !₀} {A !₁} (A !₂)
                      (corr (A !₀ , A !⁰)) (corr (A !₁ , A !¹)) × gCorr n ∙ A

-- gCorr is "actually" defined recursively on ℕᵉ.  But the successor
-- case can't be stated until we have symmetry and more computation
-- laws for ap, so we postpone it with a postulate.
postulate
  gCorr-𝐬 : (n : ℕᵉ) → ∂ (𝐬 (𝐬 n)) Type ⇒ Type

gCorr 𝐳 = ƛ A ⇒ (A !⁰ ⇒ A !¹ ⇒ Type)
gCorr (𝐬 n) = gCorr-𝐬 n

-- Here is the "primary part" of corr, the "demotion" that extracts a
-- (bitotal) correspondence from an identification in the universe.
⟦_⟧ : {X₀ X₁ : Type} (X₂ : X₀ ＝ X₁) → X₀ ⇒ X₁ ⇒ Type
⟦_⟧ {X₀} {X₁} X₂ = snd (corr {𝐬 𝐳} ((★ , ★ , ★ , X₀ , X₁) , X₂))

-- Computationally, we regard "corr 𝐳" (informally) as a DESTRUCTOR of
-- a COINDUCTIVE UNIVERSE.  This means that whenever we introduce a
-- map into the universe (i.e. a type constructor), we must specify
-- how corr computes on it.  Giving such a computation law for a
-- particular type former amounts to specifying its identity types
-- along with its transport and lifting, which will generally be
-- instances of the same type former (so that this is morally a
-- corecursive definition, matching the coinductive nature of the
-- universe).

-- This also means that ap-corr, ap-ap-corr, and so on ought also to be
-- regarded as coinductive destructors (of ＝U, SqU, and so on).  In
-- particular, the computation laws for "corr" on type-formers should
-- lift to computation laws of ap-corr.  We will enforce this by
-- computing iterated ap/refl on type formers to a "corecursive
-- constructor" of higher cubes in the universe that essentially
-- specifies the output of higher "corr"s on itself.

-- The fact that ap-corr is (informally) the destructor of a
-- coinductive ＝U means that it's sensible to add an additional
-- constructor of ＝U as long as we specify how ap-corr computes on
-- it.  This will be the "promotion" rule taking a one-to-one
-- correspondence to an identification in the universe.

-- Intuitively, we can say that while Book HoTT specifies ∞-groupoid
-- structure *inductively*, and cubical type theory specifies it
-- *explicitly*, HOTT specifies it *coinductively*.

--------------------------------------------------
-- Comparing correspondences to identifications
--------------------------------------------------

-- The correspondence of (refl A) is the identity types of A, and
-- similarly the correspondence of (ap B a₂) is the dependent identity
-- type (Id B a₂).  Note that we rewrite the identity types to ⟦refl⟧
-- and ⟦ap⟧, not the other way around!  It's a bit annoying that from
-- now on, we won't see any ＝s or Ids in normalized output.  But it's
-- great for making functoriality automatic.
postulate
  ＝-⟦refl⟧ : (A : Type) (a₀ a₁ : A) → (a₀ ＝ a₁) ≡ ⟦ refl A ⟧ ∙ a₀ ∙ a₁
  Id-⟦ap⟧ : {A : Type} (B : A → Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁)
    (b₀ : B a₀) (b₁ : B a₁) →
    Id B a₂ b₀ b₁ ≡ ⟦ ap B a₂ ⟧ ∙ b₀ ∙ b₁
{-# REWRITE ＝-⟦refl⟧ Id-⟦ap⟧ #-}
