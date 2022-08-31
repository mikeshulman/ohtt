{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Square.Heterogeneous.Base where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube
open import HOTT.Universe
open import HOTT.Functoriality
open import HOTT.Square.Simple
open import HOTT.Sigma5

------------------------------
-- Id-Id in the universe
------------------------------

-- This is the identity types of ≊, computed as if it were a Σ-type.
-- TODO: This needs to be a datatype too.  And, of course, its identity types...
record Id≊ {A₀₀ A₀₁ : Type} (A₀₂ : A₀₀ ＝ A₀₁) {A₁₀ A₁₁ : Type} (A₁₂ : A₁₀ ＝ A₁₁)
  (A₂₀ : A₀₀ ≊ A₁₀) (A₂₁ : A₀₁ ≊ A₁₁) : Type where
  constructor Id≊[_,_,_,_,_]
  field
    ap-／ : {a₀₀ : A₀₀} {a₀₁ : A₀₁} (a₀₂ : A₀₂ ↓ ／ a₀₀ ～ a₀₁)
            {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a₁₂ : A₁₂ ↓ ／ a₁₀ ～ a₁₁) →
            (A₂₀ ／ a₀₀ ～ a₁₀) ＝ (A₂₁ ／ a₀₁ ～ a₁₁)
    ap-coe→ : {a₀₀ : A₀₀} {a₀₁ : A₀₁} (a₀₂ : A₀₂ ↓ ／ a₀₀ ～ a₀₁) →
      A₁₂ ↓ ／ coe⇒ A₂₀ ∙ a₀₀ ～ coe⇒ A₂₁ ∙ a₀₁
    ap-coe← : {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a₁₂ : A₁₂ ↓ ／ a₁₀ ～ a₁₁) →
      A₀₂ ↓ ／ coe⇐ A₂₀ ∙ a₁₀ ～ coe⇐ A₂₁ ∙ a₁₁
    ap-push→ : {a₀₀ : A₀₀} {a₀₁ : A₀₁} (a₀₂ : A₀₂ ↓ ／ a₀₀ ～ a₀₁) →
      ap-／ a₀₂ (ap-coe→ a₀₂) ↓ ／ push⇒ A₂₀ ∙ a₀₀ ～ push⇒ A₂₁ ∙ a₀₁
    ap-push← : {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a₁₂ : A₁₂ ↓ ／ a₁₀ ～ a₁₁) →
      ap-／ (ap-coe← a₁₂) a₁₂ ↓ ／ push⇐ A₂₀ ∙ a₁₀ ～ push⇐ A₂₁ ∙ a₁₁
open Id≊ public

postulate
  ＝-≊ : {A B : Type} (e₀ e₁ : A ≊ B) →
    (e₀ ＝ e₁) ≡ Id≊ (refl A) (refl B) e₀ e₁
  Id-≊ : {Δ : Type} (A B : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (e₀ : A δ₀ ≊ B δ₀) (e₁ : A δ₁ ≊ B δ₁) →
    Id (λ δ → A δ ≊ B δ) δ₂ e₀ e₁ ≡ Id≊ (ap A δ₂) (ap B δ₂) e₀ e₁
{-# REWRITE ＝-≊ Id-≊ #-}

-- TODO: compute ap and refl on all the constructors and fields of ≊.
-- Also deal with the higher identity types of ≊ too.

-- Here's part of this, an Id analogue of the putative ap on _／_～_.
postulate
  Id-／ : {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (A B : Δ → Type) (e : (δ : Δ) → A δ ≊ B δ)
    (a : (δ : Δ) → A δ) (b : (δ : Δ) → B δ)
    (u₀ : e δ₀ ／ a δ₀ ～ b δ₀) (u₁ : e δ₁ ／ a δ₁ ～ b δ₁) →
    Id (λ δ → e δ ／ a δ ～ b δ) δ₂ u₀ u₁ ≡
    (snd (kan {𝐬 𝐳} (★ ⸴ ★ ⸴ ★ ⸴ _ ⸴ _ , ap-／ (ap e δ₂) (ap a δ₂) (ap b δ₂))) ／ u₀ ～ u₁)
{-# REWRITE Id-／ #-}

------------------------------
-- Computing gKan on 𝐬
------------------------------

postulate
  gKan-𝐬 : (n : ℕᵉ) → gKan (𝐬 n) ≡ ƛ A ⇒
    Id (gKan n ∙_)
    {A !₀ !₀ ⸴ A !₁ !₀ ⸴ A !₂ !₀ ⸴ A !₀ !⁰ ⸴ A !₁ !⁰}
    {A !₀ !₁ ⸴ A !₁ !₁ ⸴ A !₂ !₁ ⸴ A !₀ !¹ ⸴ A !₁ !¹}
    (A !₀ !₂ ⸴ A !₁ !₂ ⸴
    sym (∂ n Type) ┌─    A !₂ !₁    ─┐
                   A !₀ !₂  □  A !₁ !₂
                   └─    A !₂ !₀    ─┘ (A !₂ !₂) ⸴
    A !⁰ ⸴ A !¹)
    (snd (kan {𝐬 n} (A !₀ !₀ ⸴ A !₁ !₀ ⸴ A !₂ !₀ ⸴ A !₀ !⁰ ⸴ A !₁ !⁰ , A !₂ !⁰)))
    (snd (kan {𝐬 n} (A !₀ !₁ ⸴ A !₁ !₁ ⸴ A !₂ !₁ ⸴ A !₀ !¹ ⸴ A !₁ !¹ , A !₂ !¹)))
{-# REWRITE gKan-𝐬 #-}

----------------------------------------
-- Heterogeneous squares
----------------------------------------

record ∂2ʰ {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  (a₀₀ : A₀₀) (a₀₁ : A₀₁) (a₁₀ : A₁₀) (a₁₁ : A₁₁) : Typeᵉ where
  constructor ┏━_━┓_□_┗━_━┛
  infix 70 _₁₂ _₂₀ _₂₁ _₀₂
  field
    _₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁
    _₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀
    _₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁
    _₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁
open ∂2ʰ public

sym-∂2ʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} {A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁} {A₂₂ : Sq Type A}
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} →
  ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁ → ∂2ʰ (sym-∂2 A) (sym Type A A₂₂) a₀₀ a₁₀ a₀₁ a₁₁
sym-∂2ʰ a = ┏━   a ₂₁   ━┓
            a ₀₂  □   a ₁₂
            ┗━   a ₂₀   ━┛

Sqʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) → Type
Sqʰ {A₀₀} {A₀₁} {A₁₀} {A₁₁} A A₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  ap-／ {A₀₀} {A₀₁} {A ₀₂} {A₁₀} {A₁₁} {A ₁₂} {A ₂₀ ↓} {A ₂₁ ↓}
    (snd (fst (kan {𝐬 (𝐬 𝐳)} ((★ ⸴ ★ ⸴ ★ ⸴ A₀₀ ⸴ A₁₀) ⸴ (★ ⸴ ★ ⸴ ★ ⸴ A₀₁ ⸴ A₁₁) ⸴ (★ ⸴ ★ ⸴ ★ ⸴ A ₀₂ ⸴ A ₁₂) ⸴ A ₂₀ ⸴ A ₂₁ ,
      →Id-ap {∂ (𝐬 𝐳) Type} {Type × Type} (λ A → A !⁰ , A !¹) (ƛ u ⇒ fst u ＝ snd u)
             {★ ⸴ ★ ⸴ ★ ⸴ A₀₀ ⸴ A₁₀} {★ ⸴ ★ ⸴ ★ ⸴ A₀₁ ⸴ A₁₁} (★ ⸴ ★ ⸴ ★ ⸴ A ₀₂ ⸴ A ₁₂) {A ₂₀} {A ₂₁} A₂₂))))
    {a₀₀} {a₀₁} (a ₀₂) {a₁₀} {a₁₁} (a ₁₂) ↓ ／ a ₂₀ ～ (a ₂₁)

-- The other component of kan is a primitive symmetrized square.  The
-- two are interchanged by symmetry acting on U, and are isomorphic to
-- each other by a postulated heterogeneous symmetry.

Symʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) → Type
Symʰ {A₀₀} {A₀₁} {A₁₀} {A₁₁} A A₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  ap-／ {A₀₀} {A₁₀} {A ₂₀} {A₀₁} {A₁₁} {A ₂₁} {A ₀₂ ↓} {A ₁₂ ↓}
    (snd (kan {𝐬 (𝐬 𝐳)} ((★ ⸴ ★ ⸴ ★ ⸴ A₀₀ ⸴ A₁₀) ⸴ (★ ⸴ ★ ⸴ ★ ⸴ A₀₁ ⸴ A₁₁) ⸴ (★ ⸴ ★ ⸴ ★ ⸴ A ₀₂ ⸴ A ₁₂) ⸴ A ₂₀ ⸴ A ₂₁ ,
      →Id-ap {∂ (𝐬 𝐳) Type} {Type × Type} (λ A → A !⁰ , A !¹) (ƛ u ⇒ fst u ＝ snd u)
             {★ ⸴ ★ ⸴ ★ ⸴ A₀₀ ⸴ A₁₀} {★ ⸴ ★ ⸴ ★ ⸴ A₀₁ ⸴ A₁₁} (★ ⸴ ★ ⸴ ★ ⸴ A ₀₂ ⸴ A ₁₂) {A ₂₀} {A ₂₁} A₂₂)))
    {a₀₀} {a₁₀} (a ₂₀) {a₀₁} {a₁₁} (a ₂₁) ↓ ／ a ₀₂ ～ (a ₁₂)

-- TODO: Heterogeneous squares in refl-refl are ordinary squares

-- TODO: Heterogeneous squares in ap-ap are dependent squares
