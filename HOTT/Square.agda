{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --allow-unsolved-metas #-}

module HOTT.Square where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

------------------------------
-- Total identity telescopes
------------------------------

-- The "total identity telescope" of a telescope is the "free path
-- space", whose elements are two elements of Δ together with an
-- identification between them.
TID : Tel → Tel
TID Δ = PROD Δ Δ ► (λ w₀w₁ → ID Δ (FST Δ Δ w₀w₁) (SND Δ Δ w₀w₁))

left : {Δ : Tel} → el (TID Δ) → el Δ
left {Δ} w = FST Δ Δ (POP (λ w₀w₁ → ID Δ (FST Δ Δ w₀w₁) (SND Δ Δ w₀w₁)) w)

right : {Δ : Tel} → el (TID Δ) → el Δ
right {Δ} w = SND Δ Δ (POP (λ w₀w₁ → ID Δ (FST Δ Δ w₀w₁) (SND Δ Δ w₀w₁)) w)

mid : {Δ : Tel} (w : el (TID Δ)) → el (ID Δ (left w) (right w))
mid {Δ} w = TOP (λ w₀w₁ → ID Δ (FST Δ Δ w₀w₁) (SND Δ Δ w₀w₁)) w

tot : {Δ : Tel} (δ₀ δ₁ : el Δ) (δ₂ : el (ID Δ δ₀ δ₁)) → el (TID Δ)
tot {Δ} δ₀ δ₁ δ₂ = PAIR (λ w₀w₁ → ID Δ (FST Δ Δ w₀w₁) (SND Δ Δ w₀w₁)) (PR Δ Δ δ₀ δ₁) δ₂

TID′ : {Θ : Tel} (Δ : el Θ → Tel) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → Tel
TID′ {Θ} Δ {t₀} {t₁} t₂ = PROD (Δ t₀) (Δ t₁) ► (λ w₀w₁ → ID′ Δ t₂ (FST (Δ t₀) (Δ t₁) w₀w₁) (SND (Δ t₀) (Δ t₁) w₀w₁))

left′ : {Θ : Tel} (Δ : el Θ → Tel) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → el (TID′ Δ t₂) → el (Δ t₀)
left′ Δ {t₀} {t₁} t₂ δ = FST (Δ t₀) (Δ t₁) (POP (λ w₀w₁ → ID′ Δ t₂ (FST (Δ t₀) (Δ t₁) w₀w₁) (SND (Δ t₀) (Δ t₁) w₀w₁)) δ)

right′ : {Θ : Tel} (Δ : el Θ → Tel) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → el (TID′ Δ t₂) → el (Δ t₁)
right′ Δ {t₀} {t₁} t₂ δ = SND (Δ t₀) (Δ t₁) (POP (λ w₀w₁ → ID′ Δ t₂ (FST (Δ t₀) (Δ t₁) w₀w₁) (SND (Δ t₀) (Δ t₁) w₀w₁)) δ)

mid′ : {Θ : Tel} (Δ : el Θ → Tel) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) (δ : el (TID′ Δ t₂)) → el (ID′ Δ t₂ (left′ Δ t₂ δ) (right′ Δ t₂ δ))
mid′ Δ {t₀} {t₁} t₂ δ = TOP (λ w₀w₁ → ID′ Δ t₂ (FST (Δ t₀) (Δ t₁) w₀w₁) (SND (Δ t₀) (Δ t₁) w₀w₁)) δ

tot′ : {Θ : Tel} (Δ : el Θ → Tel) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
       (δ₀ : el (Δ t₀)) (δ₁ : el (Δ t₁)) (δ₂ : el (ID′ Δ t₂ δ₀ δ₁)) → el (TID′ Δ t₂)
tot′ Δ {t₀} {t₁} t₂ δ₀ δ₁ δ₂ = PAIR (λ w₀w₁ → ID′ Δ t₂ (FST (Δ t₀) (Δ t₁) w₀w₁) (SND (Δ t₀) (Δ t₁) w₀w₁)) (PR (Δ t₀) (Δ t₁) δ₀ δ₁) δ₂

TID″ : {Θ : Tel} (Δ : el Θ → Tel) (t : el (TID Θ)) → Tel
TID″ {Θ} Δ t = TID′ Δ {left t} {right t} (mid {Θ} t)

-- The uncurried identity telescope
UID : (Δ : Tel) (w : el (PROD Δ Δ)) → Tel
UID Δ w = ID Δ (FST Δ Δ w) (SND Δ Δ w)

--------------------
-- Squares
--------------------

SQ : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) → Tel
SQ Δ {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ =
  ID′ (UID Δ) {PR Δ Δ δ₀₀ δ₁₀} {PR Δ Δ δ₀₁ δ₁₁}
      (PAIR {ID Δ δ₀₀ δ₀₁} (λ w → ID′ {Δ} (λ _ → Δ) w δ₁₀ δ₁₁) δ₀₂ (COE← (ID′-CONST {Δ} Δ δ₀₂ δ₁₀ δ₁₁) δ₁₂))
      δ₂₀ δ₂₁

-- Given the top and bottom of a square, this "total left-right
-- identity telescope" includes a left and right plus a filler.
TSQ-LR : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁)) → Tel
TSQ-LR Δ {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ =
  TID′ (UID Δ) {PR Δ Δ δ₀₀ δ₁₀} {PR Δ Δ δ₀₁ δ₁₁}
       (PAIR {ID Δ δ₀₀ δ₀₁} (λ w → ID′ {Δ} (λ _ → Δ) w δ₁₀ δ₁₁) δ₀₂ (COE← (ID′-CONST {Δ} Δ δ₀₂ δ₁₀ δ₁₁) δ₁₂))

-- Similarly, given the left and right of a square, the "total
-- top-bottom identity telescope" includes a top and bottom plus a
-- filler.
TSQ-TB : (Δ : Tel) {δ₀₀ δ₀₁ δ₁₀ δ₁₁ : el Δ} (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) → Tel
TSQ-TB Δ {δ₀₀} {δ₀₁} {δ₁₀} {δ₁₁} δ₂₀ δ₂₁ = ID (TID Δ) (tot δ₀₀ δ₁₀ δ₂₀) (tot δ₀₁ δ₁₁ δ₂₁)

tsq-tb : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁)) →
  el (TSQ-TB Δ δ₂₀ δ₂₁)
tsq-tb Δ {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ =
  PAIR (λ w₂ → ID′ (UID Δ) {PR Δ Δ δ₀₀ δ₁₀} {PR Δ Δ δ₀₁ δ₁₁} w₂ δ₂₀ δ₂₁)
       (PAIR {ID Δ δ₀₀ δ₀₁} (λ w → ID′ {Δ} (λ _ → Δ) w δ₁₀ δ₁₁) δ₀₂ (COE← (ID′-CONST {Δ} Δ δ₀₂ δ₁₀ δ₁₁) δ₁₂)) δ₂₂

-- Given a type dependent on Δ, we can lift a top-bottom identity
-- telescope to that type with a pair of appropriate identifications,
-- leaving the left and right boundaries empty.
tsq-tb-lift : (Δ : Tel) (A : el Δ → Type) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁) →
  el (TSQ-TB Δ δ₂₀ δ₂₁
    ▸ (λ w → Id′ {TID Δ} (λ z → A (left z)) {tot δ₀₀ δ₁₀ δ₂₀} {tot δ₀₁ δ₁₁ δ₂₁} w a₀₀ a₀₁)
    ▸ (λ w → Id′ {TID Δ ▸ (λ z → A (left z))} (λ z → A (right (pop z))) {tot δ₀₀ δ₁₀ δ₂₀ ∷ a₀₀} {tot δ₀₁ δ₁₁ δ₂₁ ∷ a₀₁} w a₁₀ a₁₁))
tsq-tb-lift Δ A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ =
  tsq-tb Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂
         ∷ coe→ (Id′-AP (λ w → left w) {tot δ₀₀ δ₁₀ δ₂₀} {tot δ₀₁ δ₁₁ δ₂₁} (tsq-tb Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) A a₀₀ a₀₁) a₀₂
         ∷ coe→ (Id′-AP (λ z → right (pop z)) {tot δ₀₀ δ₁₀ δ₂₀ ∷ a₀₀} {tot δ₀₁ δ₁₁ δ₂₁ ∷ a₀₁}
                       (tsq-tb Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ ∷
                        coe→ (Id′-AP (λ w → left w)
                                     {PAIR {PROD Δ Δ} (UID Δ) (PR Δ Δ δ₀₀ δ₁₀) δ₂₀}
                                     {PAIR {PROD Δ Δ} (UID Δ) (PR Δ Δ δ₀₁ δ₁₁) δ₂₁}
                                     (tsq-tb Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) A a₀₀ a₀₁) a₀₂)
                       A a₁₀ a₁₁)
                 (coe← (cong (λ e → Id′ A e a₁₀ a₁₁) (coe→coe←ᵉ (cong el (ID′-CONST {Δ} Δ {δ₀₀} {δ₀₁} δ₀₂ δ₁₀ δ₁₁)))) a₁₂)

-- Finally, with these auxiliary supporting definitions, we can define
-- a square in a type dependent on a square in a telescope.
Sq : {Δ : Tel} (A : el Δ → Type) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
     (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
     {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
     (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) → Type
Sq {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id′ {TID Δ ▸ (λ w → A (left w)) ▸ (λ w → A (right (pop w)))}
      (λ w → Id′ {Δ} A (mid {Δ} (pop (pop w))) (top (pop w)) (top w))
      {tot δ₀₀ δ₁₀ δ₂₀ ∷ a₀₀ ∷ a₁₀} {tot δ₀₁ δ₁₁ δ₂₁ ∷ a₀₁ ∷ a₁₁}
      (tsq-tb-lift Δ A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂)
      a₂₀ a₂₁

