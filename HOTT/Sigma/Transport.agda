{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Sigma.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Transport
open import HOTT.Fill
open import HOTT.Sigma.Base

----------------------------------------
-- Transport in Σ-types
----------------------------------------

postulate
  tr→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (B (δ ₀))) →
    tr→ (Λ w ⇨ Σ (A w) (B w)) δ u₀ ≡
    (tr→ (Λ⇨ A) δ (fst u₀) ,
     tr→ {Δ ▸ (Λ⇨ A)} (Λ⇨ (uncurry {A = Λ⇨ A} B))
         (δ ∷ fst u₀ ∷ tr→ (Λ⇨ A) δ (fst u₀) ∷ lift→ (Λ⇨ A) δ (fst u₀))
         (snd u₀))
  tr←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₁ : Σ (A (δ ₁)) (B (δ ₁))) →
    tr← (Λ w ⇨ Σ (A w) (B w)) δ u₁ ≡
    (tr← (Λ⇨ A) δ (fst u₁) ,
     tr← {Δ ▸ (Λ⇨ A)} (Λ⇨ (uncurry {A = Λ⇨ A} B))
         (δ ∷ tr← (Λ⇨ A) δ (fst u₁) ∷ fst u₁ ∷ lift← (Λ⇨ A) δ (fst u₁))
         (snd u₁))

{-# REWRITE tr→Σ tr←Σ #-}

postulate
  lift→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (B (δ ₀))) →
    lift→ (Λ w ⇨ Σ (A w) (B w)) δ u₀ ≡
    (lift→ (Λ⇨ A) δ (fst u₀) ,
     lift→ {Δ ▸ (Λ⇨ A)} (Λ⇨ (uncurry {A = Λ⇨ A} B))
           (δ ∷ fst u₀ ∷ tr→ (Λ⇨ A) δ (fst u₀) ∷ lift→ (Λ⇨ A) δ (fst u₀))
           (snd u₀))
  lift←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₁ : Σ (A (δ ₁)) (B (δ ₁))) →
    lift← (Λ w ⇨ Σ (A w) (B w)) δ u₁ ≡
    (lift← (Λ⇨ A) δ (fst u₁) ,
     lift← {Δ ▸ (Λ⇨ A)} (Λ⇨ (uncurry {A = Λ⇨ A} B))
           (δ ∷ tr← (Λ⇨ A) δ (fst u₁) ∷ fst u₁ ∷ lift← (Λ⇨ A) δ (fst u₁))
           (snd u₁))

{-# REWRITE lift→Σ lift←Σ #-}

-- Once we've defined tr and lift for Σ-types, we can deduce utr and
-- ulift from square-filling.  Since that involves transport in an
-- identity type of a Σ-type, which is again a Σ-type, the above
-- definitions should suffice to compute it.

postulate
  utr→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₀ : Σ (A (δ ₀)) (B (δ ₀))) (u₁ u₁' : Σ (A (δ ₁)) (B (δ ₁)))
    (u₂ : Id (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁') →
    utr→      (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    fill-utr→ (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂'
  utr←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₁ : Σ (A (δ ₁)) (B (δ ₁))) (u₀ u₀' : Σ (A (δ ₀)) (B (δ ₀)))
    (u₂ : Id (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id (Λ w ⇨ Σ (A w) (B w)) δ u₀' u₁) →
    utr←      (Λ w ⇨ Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    fill-utr← (Λ w ⇨ Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂'

{-# REWRITE utr→Σ utr←Σ #-}

postulate
  ulift→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₀ : Σ (A (δ ₀)) (B (δ ₀))) (u₁ u₁' : Σ (A (δ ₁)) (B (δ ₁)))
    (u₂ : Id (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁') →
    ulift→      (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    fill-ulift→ (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂'
  ulift←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₁ : Σ (A (δ ₁)) (B (δ ₁))) (u₀ u₀' : Σ (A (δ ₀)) (B (δ ₀)))
    (u₂ : Id (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id (Λ w ⇨ Σ (A w) (B w)) δ u₀' u₁) →
    ulift←      (Λ w ⇨ Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    fill-ulift← (Λ w ⇨ Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂'

{-# REWRITE ulift→Σ ulift←Σ #-}
