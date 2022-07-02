{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Universe where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
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
    (ap (Λ _ ⇨ Type) A δ) ↓ ≡
    ((ƛ a₀ ⇒ ƛ a₁ ⇒ Id (Λ⇨ A) δ a₀ a₁) ,
    ((ƛ a₀ ⇒ (tr→ (Λ⇨ A) δ a₀ , lift→ (Λ⇨ A) δ a₀) ,
              (ƛ x ⇒ ƛ x' ⇒ (utr→ (Λ⇨ A) δ a₀ (fst x) (fst x') (snd x) (snd x') ,
                             ulift→ (Λ⇨ A) δ a₀ (fst x) (fst x') (snd x) (snd x')))) ,
     (ƛ a₁ ⇒ (tr← (Λ⇨ A) δ a₁ , lift← (Λ⇨ A) δ a₁) ,
              (ƛ x ⇒ ƛ x' ⇒ (utr← (Λ⇨ A) δ a₁ (fst x) (fst x') (snd x) (snd x') ,
                             ulift← (Λ⇨ A) δ a₁ (fst x) (fst x') (snd x) (snd x'))))))

{-# REWRITE apU #-}

-- TODO: Id-top, the Tarski eliminator
