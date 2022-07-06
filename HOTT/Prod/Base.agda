{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-projection-like #-}

module HOTT.Prod.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl

infix 35 _×_

--------------------
-- Product types
--------------------

-- It may seem that we should derive these from Σ-types, but various
-- things simplify in the non-dependent case, so I think it's worth
-- defining them separately.

data _×_ (A B : Type) : Type where
  _,_ : A → B → A × B


fst : {A : Type} {B : Type} → A × B → A
fst (a , b) = a

snd : {A : Type} {B : Type} → A × B → B
snd (a , b) = b

postulate
  η, : (A : Type) (B : Type) (u : A × B) → (fst u , snd u) ≡ u
  ＝× : (A B : Type) (u v : A × B) →
    (u ＝ v) ≡ (fst u ＝ fst v) × (snd u ＝ snd v)
  Id× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
        (u : A (δ ₀) × B (δ ₀)) (v : A (δ ₁) × B (δ ₁)) →
    Id (Λ w ⇨ A w × B w) δ u v ≡
    Id (Λ⇨ A) δ (fst u) (fst v) × Id (Λ⇨ B) δ (snd u) (snd v)

{-# REWRITE η, ＝× Id× #-}

postulate
  ap, : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f : (x : el Δ) → A x) (g : (x : el Δ) → B x) →
    ap (Λ w ⇨ A w × B w) (λ x → (f x , g x)) δ ≡
    (ap (Λ⇨ A) f δ , ap (Λ⇨ B) g δ)
  ap-fst : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f : (x : el Δ) → A x × B x) →
    ap (Λ⇨ A) (λ x → fst (f x)) δ ≡ fst (ap (Λ w ⇨ A w × B w) f δ)
  ap-snd : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f : (x : el Δ) → A x × B x) →
    ap (Λ⇨ B) (λ x → snd (f x)) δ ≡ snd (ap (Λ w ⇨ A w × B w) f δ)
  refl, : {A B : Type} (a : A) (b : B) → refl (a , b) ≡ (refl a , refl b)
  refl-fst : {A B : Type} (u : A × B) → refl (fst u) ≡ fst (refl u)
  refl-snd : {A B : Type} (u : A × B) → refl (snd u) ≡ snd (refl u)

{-# REWRITE ap, ap-fst ap-snd refl, refl-fst refl-snd #-}
