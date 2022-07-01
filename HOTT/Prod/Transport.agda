{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --cumulativity #-}

module HOTT.Prod.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Prod.Base

----------------------------------------
-- Transport in product types
----------------------------------------

postulate
  tr→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₀ : A (δ ₀) × B (δ ₀)) →
    tr→ (Λ w ⇨ A w × B w) δ u₀ ≡ (tr→ (Λ⇨ A) δ (fst u₀) , tr→ (Λ⇨ B) δ (snd u₀))
  tr←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₁ : A (δ ₁) × B (δ ₁)) →
    tr← (Λ w ⇨ A w × B w) δ u₁ ≡ (tr← (Λ⇨ A) δ (fst u₁) , tr← (Λ⇨ B) δ (snd u₁))

{-# REWRITE tr→× tr←× #-}

postulate
  lift→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₀ : A (δ ₀) × B (δ ₀)) →
    lift→ (Λ w ⇨ A w × B w) δ u₀ ≡ (lift→ (Λ⇨ A) δ (fst u₀) , lift→ (Λ⇨ B) δ (snd u₀))
  lift←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₁ : A (δ ₁) × B (δ ₁)) →
    lift← (Λ w ⇨ A w × B w) δ u₁ ≡ (lift← (Λ⇨ A) δ (fst u₁) , lift← (Λ⇨ B) δ (snd u₁))

{-# REWRITE lift→× lift←× #-}

-- Product types are still simple enough that it's feasible to define
-- utr and ulift explicitly rather than by way of square composites
-- and filling.  We do this to make the point.

postulate
  utr→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : A (δ ₀) × B (δ ₀)) (u₁ u₁' : A (δ ₁) × B (δ ₁))
    (u₂ : Id (Λ w ⇨ A w × B w) δ u₀ u₁) (u₂' : Id (Λ w ⇨ A w × B w) δ u₀ u₁') →
    utr→ (Λ w ⇨ A w × B w) δ u₀ u₁ u₁' u₂ u₂' ≡
    (utr→ (Λ⇨ A) δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') , utr→ (Λ⇨ B) δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂'))
  utr←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : A (δ ₁) × B (δ ₁)) (u₀ u₀' : A (δ ₀) × B (δ ₀))
    (u₂ : Id (Λ w ⇨ A w × B w) δ u₀ u₁) (u₂' : Id (Λ w ⇨ A w × B w) δ u₀' u₁) →
    utr← (Λ w ⇨ A w × B w) δ u₁ u₀ u₀' u₂ u₂' ≡
    (utr← (Λ⇨ A) δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') , utr← (Λ⇨ B) δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂'))

{-# REWRITE utr→× utr←× #-}

postulate
  ulift→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : A (δ ₀) × B (δ ₀)) (u₁ u₁' : A (δ ₁) × B (δ ₁))
    (u₂ : Id (Λ w ⇨ A w × B w) δ u₀ u₁) (u₂' : Id (Λ w ⇨ A w × B w) δ u₀ u₁') →
    ulift→ (Λ w ⇨ A w × B w) δ u₀ u₁ u₁' u₂ u₂' ≡
    (coe← (Id-AP {ε ▸ (Λ _ ⇨ A (δ ₁) × B (δ ₁))} {ε ▸ (Λ _ ⇨ A (δ ₁))}
              (λ x → [] ∷ fst (top x))
              ([] ∷ u₁ ∷ u₁' ∷
               (utr→ (Λ⇨ A) δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') ,
                utr→ (Λ⇨ B) δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
              (Λ w ⇨ Id (Λ⇨ A) δ (fst u₀) (top w))
              (fst u₂) (fst u₂'))
           (ulift→ (Λ⇨ A) δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂')) ,
     coe← (Id-AP {ε ▸ (Λ _ ⇨ A (δ ₁) × B (δ ₁))} {ε ▸ (Λ _ ⇨ B (δ ₁))}
              (λ x → [] ∷ snd (top x))
              ([] ∷ u₁ ∷ u₁' ∷
               (utr→ (Λ⇨ A) δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') ,
                utr→ (Λ⇨ B) δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
              (Λ w ⇨ Id (Λ⇨ B) δ (snd u₀) (top w))
              (snd u₂) (snd u₂'))
           (ulift→ (Λ⇨ B) δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
  ulift←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : A (δ ₁) × B (δ ₁)) (u₀ u₀' : A (δ ₀) × B (δ ₀))
    (u₂ : Id (Λ w ⇨ A w × B w) δ u₀ u₁) (u₂' : Id (Λ w ⇨ A w × B w) δ u₀' u₁) →
    ulift← (Λ w ⇨ A w × B w) δ u₁ u₀ u₀' u₂ u₂' ≡
    (coe← (Id-AP {ε ▸ (Λ _ ⇨ A (δ ₀) × B (δ ₀))} {ε ▸ (Λ _ ⇨ A (δ ₀))}
              (λ x → [] ∷ fst (top x))
              ([] ∷ u₀ ∷ u₀' ∷
               (utr← (Λ⇨ A) δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') ,
                utr← (Λ⇨ B) δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂')))
              (Λ w ⇨ Id (Λ⇨ A) δ (top w) (fst u₁))
              (fst u₂) (fst u₂'))
           (ulift← (Λ⇨ A) δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂')),
     coe← (Id-AP {ε ▸ (Λ _ ⇨ A (δ ₀) × B (δ ₀))} {ε ▸ (Λ _ ⇨ B (δ ₀))}
              (λ x → [] ∷ snd (top x))
              ([] ∷ u₀ ∷ u₀' ∷
               (utr← (Λ⇨ A) δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') ,
                utr← (Λ⇨ B) δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂')))
              (Λ w ⇨ Id (Λ⇨ B) δ (top w) (snd u₁))
              (snd u₂) (snd u₂'))
           (ulift← (Λ⇨ B) δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂')))

{-# REWRITE ulift→× ulift←× #-}
