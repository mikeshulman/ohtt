{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Universe where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Prod
open import HOTT.Sigma
open import HOTT.Pi
open import HOTT.Copy

--------------------------------------------------
-- Contractibility and 1-1 correspondences
--------------------------------------------------

isProp : (A : Type) → Type
isProp A = Π A (λ a₀ → Π A (λ a₁ → (a₀ ＝ a₁)))

isContr : (A : Type) → Type
isContr A = A × isProp A

is11 : {A B : Type} (R : A ⇒ B ⇒ Type) → Type
is11 {A} {B} R = Π A (λ a → isContr (Σ B (λ b → R ∙ a ∙ b))) × Π B (λ b → isContr (Σ A (λ a → R ∙ a ∙ b)))

11Corr : Type → Type → Type
11Corr A B = Σ (A ⇒ B ⇒ Type) is11

------------------------------
-- The universe
------------------------------

postulate
  ＝U : (A B : Type) → (A ＝ B) ≡ Copy (11Corr A B)

{-# REWRITE ＝U #-}

postulate
  apU : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) →
    (ap A δ) ↓ ≡
    ((Λ a₀ ⇒ Λ a₁ ⇒ Id A δ a₀ a₁) ﹐
    ((Λ a₀ ⇒ (tr→ A δ a₀ ﹐ lift→ A δ a₀ ,
              Λ x ⇒ Λ x' ⇒ utr→ A δ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift→ A δ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x'))) ,
     (Λ a₁ ⇒ (tr← A δ a₁ ﹐ lift← A δ a₁ ,
              Λ x ⇒ Λ x' ⇒ utr← A δ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift← A δ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x')))))

{-# REWRITE apU #-}

-- TODO: Id-top, the Tarski eliminator
