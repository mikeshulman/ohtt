{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sigma where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Transport
--open import HOTT.Square
--open import HOTT.Sym
--open import HOTT.Square.Degenerate
--open import HOTT.Square.Extend
--open import HOTT.Fill

--------------------
-- Σ-types
--------------------

postulate
  Σ : (A : Type) → (B : A → Type) → Type
  _﹐_ : {A : Type} {B : A → Type} (a : A) → B a → Σ A B
  π₁ : {A : Type} {B : A → Type} → Σ A B → A
  π₂ : {A : Type} {B : A → Type} (u : Σ A B) → B (π₁ u)

infix 30 _﹐_

postulate
  βπ₁ : (A : Type) (B : A → Type) (a : A) (b : B a) → π₁ {B = B} (a ﹐ b) ≡ a

{-# REWRITE βπ₁ #-}

postulate
  βπ₂ : (A : Type) (B : A → Type) (a : A) (b : B a) → π₂ {B = B} (a ﹐ b) ≡ b
  η﹐ : (A : Type) (B : A → Type) (u : Σ A B) → (π₁ u ﹐ π₂ u) ≡ u

{-# REWRITE βπ₂ η﹐ #-}

postulate
  Id′Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (λ a → B (δ ₀) a)) (u₁ : Σ (A (δ ₁)) (λ a → B (δ ₁) a)) →
    Id′ {Δ} (λ w → Σ (A w) (B w)) δ u₀ u₁ ≡
    Σ (Id′ A δ (π₁ u₀) (π₁ u₁))
      (λ e → Id′ {Δ ▸ A} (uncurry B) (δ ∷ π₁ u₀ ∷ π₁ u₁ ∷ e) (π₂ u₀) (π₂ u₁))
  IdΣ : (A : Type) (B : A → Type) (u₀ u₁ : Σ A B) →
    Id (Σ A B) u₀ u₁ ≡
    Σ (Id A (π₁ u₀) (π₁ u₁))
      (λ e → Id′ {ε ▸ (λ _ → A)} (λ a → B (top a)) ([] ∷ π₁ u₀ ∷ π₁ u₁ ∷ e) (π₂ u₀) (π₂ u₁))

{-# REWRITE Id′Σ IdΣ #-}

postulate
  ap﹐ : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type} (f : (δ : el Δ) → A δ) (g : (δ : el Δ) → B δ (f δ))
    (δ : el (ID Δ)) →
    ap {A = λ w → Σ (A w) (B w)} (λ w → f w ﹐ g w) δ ≡
    (ap f δ ﹐  coe→ (Id′-AP (λ w → (w ∷ f w)) δ (uncurry B) _ _) (ap g δ))
  refl﹐ : {A : Type} {B : A → Type} (a : A) (b : B a) →
    refl {Σ A B} (a ﹐ b) ≡ (refl a ﹐ coe→ (Id′-AP {ε} (λ _ → [] ∷ a) [] (λ x → B (top x)) b b) (refl b))
  apπ₁ : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type} (δ : el (ID Δ))
    (u : (x : el Δ) → Σ (A x) (B x)) → ap (λ x → π₁ (u x)) δ ≡ π₁ (ap u δ)
  reflπ₁ : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (π₁ u) ≡ π₁ (refl u)

{-# REWRITE ap﹐ refl﹐ apπ₁ reflπ₁ #-}

-- Here we have to coerce explicitly, because matching for a rewrite would require rewriting some argument backwards.
postulate
  apπ₂ : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type} (δ : el (ID Δ))
    (u : (x : el Δ) → Σ (A x) (B x)) →
    ap (λ x → π₂ (u x)) δ ≡ coe← (Id′-AP (λ w → w ∷ π₁ (u w)) δ (uncurry B) _ _) (π₂ (ap u δ))
  reflπ₂ : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (π₂ u) ≡  coe← (Id′-AP {ε} (λ _ → [] ∷ π₁ u) [] (λ x → B (top x)) (π₂ u) (π₂ u)) (π₂ (refl u)) 

{-# REWRITE apπ₂ reflπ₂ #-}

----------------------------------------
-- Transport in Σ-types
----------------------------------------

postulate
  tr→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (B (δ ₀))) →
    tr→ (λ w → Σ (A w) (B w)) δ u₀ ≡
    (tr→ A δ (π₁ u₀) ﹐  tr→ {Δ ▸ A} (uncurry B) (δ ∷ π₁ u₀ ∷ tr→ A δ (π₁ u₀) ∷ lift→ A δ (π₁ u₀)) (π₂ u₀))
  tr←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₁ : Σ (A (δ ₁)) (B (δ ₁))) →
    tr← (λ w → Σ (A w) (B w)) δ u₁ ≡
    (tr← A δ (π₁ u₁) ﹐ tr← {Δ ▸ A} (uncurry B) (δ ∷ tr← A δ (π₁ u₁) ∷ π₁ u₁ ∷ lift← A δ (π₁ u₁)) (π₂ u₁))

{-# REWRITE tr→Σ tr←Σ #-}

postulate
  lift→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (B (δ ₀))) →
    lift→ (λ w → Σ (A w) (B w)) δ u₀ ≡
    (lift→ A δ (π₁ u₀) ﹐  lift→ {Δ ▸ A} (uncurry B) (δ ∷ π₁ u₀ ∷ tr→ A δ (π₁ u₀) ∷ lift→ A δ (π₁ u₀)) (π₂ u₀))
  lift←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₁ : Σ (A (δ ₁)) (B (δ ₁))) →
    lift← (λ w → Σ (A w) (B w)) δ u₁ ≡
    (lift← A δ (π₁ u₁) ﹐  lift← {Δ ▸ A} (uncurry B) (δ ∷ tr← A δ (π₁ u₁) ∷ π₁ u₁ ∷ lift← A δ (π₁ u₁)) (π₂ u₁))

{-# REWRITE lift→Σ lift←Σ #-}

{-
postulate
  utr→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₀ : Σ (A (δ ₀)) (B (δ ₀))) (u₁ u₁' : Σ (A (δ ₁)) (B (δ ₁)))
    (u₂ : Id′ (λ w → Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → Σ (A w) (B w)) δ u₀ u₁') →
    utr→ (λ w → Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    (utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂') ﹐
     coe← (Id′-AP {ε ▸ λ _ → A (δ ₁)} (λ x → (δ ₁) ∷ top x)
                    {[] ∷ π₁ u₁} {[] ∷ π₁ u₁'} ([] ∷ utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂'))
                    (uncurry B) (π₂ u₁) (π₂ u₁'))
        (comp→ {Δ ▸ A} (uncurry B) {(δ ₀) ∷ π₁ u₀} {(δ ₁) ∷ π₁ u₁} (δ ∷ π₁ u₂) {(δ ₀) ∷ π₁ u₀} {(δ ₁) ∷ π₁ u₁'} (δ ∷ π₁ u₂')
            (REFL (_∷_ {B = A} (δ ₀) (π₁ u₀))) (REFL (δ ₁) ∷ utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂'))
            (sq▸ A δ δ (REFL (δ ₀)) (REFL (δ ₁)) (DEGSQ-TB Δ δ)
                 (π₁ u₂) (π₁ u₂') (refl (π₁ u₀)) (utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂'))
                 (sym A (REFL (δ ₀)) (REFL (δ ₁)) δ δ (DEGSQ-LR Δ δ) (π₁ (refl u₀))
                        (utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂')) (π₁ u₂) (π₁ u₂')
                        (ulift→Sq A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂'))))
            {π₂ u₀} {π₂ u₁} (π₂ u₂) {π₂ u₀} {π₂ u₁'} (π₂ u₂')
            (coe→ (Id′-AP {ε} {Δ ▸ A} (λ _ → (δ ₀) ∷ π₁ u₀) {[]} {[]} [] (uncurry B) (π₂ u₀) (π₂ u₀)) (refl (π₂ u₀)))))
  utr←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₁ : Σ (A (δ ₁)) (B (δ ₁))) (u₀ u₀' : Σ (A (δ ₀)) (B (δ ₀)))
    (u₂ : Id′ (λ w → Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → Σ (A w) (B w)) δ u₀' u₁) →
    utr← (λ w → Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    (utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂') ﹐
     coe← (Id′-AP {ε ▸ λ _ → A (δ ₀)} (λ x → (δ ₀) ∷ top x)
                    {[] ∷ π₁ u₀} {[] ∷ π₁ u₀'} ([] ∷ utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂'))
                    (uncurry B) (π₂ u₀) (π₂ u₀'))
        (comp← {Δ ▸ A} (uncurry B) {(δ ₀) ∷ π₁ u₀} {(δ ₁) ∷ π₁ u₁} (δ ∷ π₁ u₂) {(δ ₀) ∷ π₁ u₀'} {(δ ₁) ∷ π₁ u₁} (δ ∷ π₁ u₂')
            (REFL (δ ₀) ∷ utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂')) (REFL (_∷_ {B = A} (δ ₁) (π₁ u₁)))
            (sq▸ A δ δ (REFL (δ ₀)) (REFL (δ ₁)) (DEGSQ-TB Δ δ)
                 (π₁ u₂) (π₁ u₂') (utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂')) (refl (π₁ u₁))
                 (sym A (REFL (δ ₀)) (REFL (δ ₁)) δ δ (DEGSQ-LR Δ δ)
                        (utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂'))
                        (π₁ (refl u₁)) (π₁ u₂) (π₁ u₂')
                        (ulift←Sq A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂'))))
            {π₂ u₀} {π₂ u₁} (π₂ u₂) {π₂ u₀'} {π₂ u₁} (π₂ u₂')
            (coe→ (Id′-AP {ε} {Δ ▸ A} (λ _ → (δ ₁) ∷ π₁ u₁) {[]} {[]} [] (uncurry B) (π₂ u₁) (π₂ u₁)) (refl (π₂ u₁)))))

{-# REWRITE utr→Σ utr←Σ #-}
-}
