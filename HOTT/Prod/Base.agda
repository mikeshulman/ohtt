{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Prod.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl

--------------------
-- Product types
--------------------

-- It may seem that we should derive these from Σ-types, but various
-- things simplify in the non-dependent case, so I think it's worth
-- defining them separately.

postulate
  _×_ : Type → Type → Type
  _,_ : {A : Type} {B : Type} → A → B → A × B
  fst : {A : Type} {B : Type} → A × B → A
  snd : {A : Type} {B : Type} → A × B → B

infix 30 _×_

postulate
  βfst : (A : Type) (B : Type) (a : A) (b : B) → fst (a , b) ≡ a
  βsnd : (A : Type) (B : Type) (a : A) (b : B) → snd (a , b) ≡ b
  η, : (A : Type) (B : Type) (u : A × B) → (fst u , snd u) ≡ u
  ＝× : (A B : Type) (u v : A × B) →
    (u ＝ v) ≡ (fst u ＝ fst v) × (snd u ＝ snd v)
  Id′× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u : A (δ ₀) × B (δ ₀)) (v : A (δ ₁) × B (δ ₁)) →
    Id′ (λ w → A w × B w) δ u v ≡ Id′ A δ (fst u) (fst v) × Id′ B δ (snd u) (snd v)

{-# REWRITE βfst βsnd η, ＝× Id′× #-}

postulate
  ap, : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (f : (x : el Δ) → A x) (g : (x : el Δ) → B x) →
    ap (λ x → (f x , g x)) δ ≡ (ap f δ , ap g δ)
  ap-fst : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (f : (x : el Δ) → A x × B x) →
    ap (λ x → fst (f x)) δ ≡ fst (ap f δ)
  ap-snd : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (f : (x : el Δ) → A x × B x) →
    ap (λ x → snd (f x)) δ ≡ snd (ap f δ)
  refl, : {A B : Type} (a : A) (b : B) → refl (a , b) ≡ (refl a , refl b)
  refl-fst : {A B : Type} (u : A × B) → refl (fst u) ≡ fst (refl u)
  refl-snd : {A B : Type} (u : A × B) → refl (snd u) ≡ snd (refl u)

{-# REWRITE ap, ap-fst ap-snd refl, refl-fst refl-snd #-}
