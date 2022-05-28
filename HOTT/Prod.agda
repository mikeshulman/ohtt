{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Prod where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

--------------------
-- Product types
--------------------

-- Would it work to derive these from Σ-types?

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
  Id× : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u : A δ₀ × B δ₀) (v : A δ₁ × B δ₁) →
    Id′ (λ w → A w × B w) δ₂ u v ≡ Id′ A δ₂ (fst u) (fst v) × Id′ B δ₂ (snd u) (snd v)

{-# REWRITE βfst βsnd η, Id× #-}

postulate
  ap, : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f : (x : el Δ) → A x) (g : (x : el Δ) → B x) →
    ap (λ x → (f x , g x)) δ₂ ≡ (ap f δ₂ , ap g δ₂)
  ap-fst : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f : (x : el Δ) → A x × B x) →
    ap (λ x → fst (f x)) δ₂ ≡ fst (ap f δ₂)
  ap-snd : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f : (x : el Δ) → A x × B x) →
    ap (λ x → snd (f x)) δ₂ ≡ snd (ap f δ₂)

{-# REWRITE ap, ap-fst ap-snd #-}

postulate
  Id-pop× : {Δ : Tel} (X : el Δ → Type) (A B : el Δ → Type)
    {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁))
    (u₀ : A (pop δ₀) × B (pop δ₀) ) (u₁ : A (pop δ₁) × B (pop δ₁)) →
    Id-pop X (λ w → A w × B w) {δ₀} {δ₁} δ₂ u₀ u₁ ≡
    cong2 _×_ (Id-pop X A {δ₀} {δ₁} δ₂ (fst u₀) (fst u₁)) (Id-pop X B {δ₀} {δ₁} δ₂ (snd u₀) (snd u₁))
  Id-AP× : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (A B : el Δ → Type) {u₀ : A (f t₀) × B (f t₀)} {u₁ : A (f t₁) × B (f t₁)} →
    -- Agda would accept reflᵉ as the RHS here, because Id-AP is a
    -- rewrite rule and it can fire here.  But I suspect that writing
    -- it explicitly with cong2 is better because it makes sense even
    -- if Id-AP can't be rewritten along in some case because we can't
    -- un-rewrite to get AP.
    Id-AP f t₂ (λ w → A w × B w) u₀ u₁ ≡ cong2 _×_ (Id-AP f t₂ A (fst u₀) (fst u₁)) (Id-AP f t₂ B (snd u₀) (snd u₁))

{-# REWRITE Id-pop× Id-AP× #-}

----------------------------------------
-- Transport in product types
----------------------------------------

postulate
  tr→× : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u₀ : A δ₀ × B δ₀) →
    tr→ (λ w → A w × B w) δ₂ u₀ ≡ (tr→ A δ₂ (fst u₀) , tr→ B δ₂ (snd u₀))
  tr←× : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u₁ : A δ₁ × B δ₁) →
    tr← (λ w → A w × B w) δ₂ u₁ ≡ (tr← A δ₂ (fst u₁) , tr← B δ₂ (snd u₁))

{-# REWRITE tr→× tr←× #-}

postulate
  lift→× : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u₀ : A δ₀ × B δ₀) →
    lift→ (λ w → A w × B w) δ₂ u₀ ≡ (lift→ A δ₂ (fst u₀) , lift→ B δ₂ (snd u₀))
  lift←× : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u₁ : A δ₁ × B δ₁) →
    lift← (λ w → A w × B w) δ₂ u₁ ≡ (lift← A δ₂ (fst u₁) , lift← B δ₂ (snd u₁))

{-# REWRITE lift→× lift←× #-}

postulate
  utr→× : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (u₀ : A δ₀ × B δ₀) (u₁ u₁' : A δ₁ × B δ₁)
    (u₂ : Id′ (λ w → A w × B w) δ₂ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ₂ u₀ u₁') →
    utr→ (λ w → A w × B w) δ₂ u₀ u₁ u₁' u₂ u₂' ≡
    (utr→ A δ₂ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') , utr→ B δ₂ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂'))
  utr←× : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (u₁ : A δ₁ × B δ₁) (u₀ u₀' : A δ₀ × B δ₀)
    (u₂ : Id′ (λ w → A w × B w) δ₂ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ₂ u₀' u₁) →
    utr← (λ w → A w × B w) δ₂ u₁ u₀ u₀' u₂ u₂' ≡
    (utr← A δ₂ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') , utr← B δ₂ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂'))

{-# REWRITE utr→× utr←× #-}

postulate
  ulift→× : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (u₀ : A δ₀ × B δ₀) (u₁ u₁' : A δ₁ × B δ₁)
    (u₂ : Id′ (λ w → A w × B w) δ₂ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ₂ u₀ u₁') →
    ulift→ (λ w → A w × B w) δ₂ u₀ u₁ u₁' u₂ u₂' ≡
    (coe→
      (Id-AP {ε ▸ (λ _ → A δ₁ × B δ₁)} {ε ▸ (λ _ → A δ₁)} (λ w → (pop w ∷ fst (top w))) {[] ∷ u₁} {[] ∷ u₁'}
        ([] ∷ (utr→ (λ z → A z) δ₂ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') ,
               utr→ (λ z → B z) δ₂ (snd u₀) (snd u₁) (snd u₁') (snd u₂)  (snd u₂')))
        (λ w → Id′ A δ₂ (fst u₀) (top w)) (fst u₂) (fst u₂'))
      (ulift→ A δ₂ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂')) ,
     coe→
      (Id-AP {ε ▸ (λ _ → A δ₁ × B δ₁)} {ε ▸ (λ _ → B δ₁)} (λ w → (pop w ∷ snd (top w))) {[] ∷ u₁} {[] ∷ u₁'}
        ([] ∷ (utr→ (λ z → A z) δ₂ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') ,
               utr→ (λ z → B z) δ₂ (snd u₀) (snd u₁) (snd u₁') (snd u₂)  (snd u₂')))
        (λ w → Id′ B δ₂ (snd u₀) (top w)) (snd u₂) (snd u₂'))
      (ulift→ B δ₂ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
  ulift←× : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (u₁ : A δ₁ × B δ₁) (u₀ u₀' : A δ₀ × B δ₀)
    (u₂ : Id′ (λ w → A w × B w) δ₂ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ₂ u₀' u₁) →
    ulift← (λ w → A w × B w) δ₂ u₁ u₀ u₀' u₂ u₂' ≡
    (coe→
      (Id-AP {ε ▸ (λ _ → A δ₀ × B δ₀)} {ε ▸ (λ _ → A δ₀)} (λ w → (pop w ∷ fst (top w))) {[] ∷ u₀} {[] ∷ u₀'}
        ([] ∷ (utr← (λ z → A z) δ₂ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') ,
               utr← (λ z → B z) δ₂ (snd u₁) (snd u₀) (snd u₀') (snd u₂)  (snd u₂')))
        (λ w → Id′ A δ₂ (top w) (fst u₁)) (fst u₂) (fst u₂'))
      (ulift← A δ₂ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂')) ,
     coe→
      (Id-AP {ε ▸ (λ _ → A δ₀ × B δ₀)} {ε ▸ (λ _ → B δ₀)} (λ w → (pop w ∷ snd (top w))) {[] ∷ u₀} {[] ∷ u₀'}
        ([] ∷ (utr← (λ z → A z) δ₂ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') ,
               utr← (λ z → B z) δ₂ (snd u₁) (snd u₀) (snd u₀') (snd u₂)  (snd u₂')))
        (λ w → Id′ B δ₂ (top w) (snd u₁)) (snd u₂) (snd u₂'))
      (ulift← B δ₂ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂')))

{-# REWRITE ulift→× ulift←× #-}

