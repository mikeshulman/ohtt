{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

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
tot {Δ} δ₀ δ₁ δ₂ = PAIR (λ w₀w₁ → ID Δ (FST Δ Δ w₀w₁) (SND Δ Δ w₀w₁)) (PAIR (λ _ → Δ) δ₀ δ₁) δ₂

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

-- The curried identity telescope
CID : (Δ : Tel) (w : el (PROD Δ Δ)) → Tel
CID Δ w = ID Δ (FST Δ Δ w) (SND Δ Δ w)

--------------------
-- Squares
--------------------

SQ : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) → Tel
SQ Δ {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ =
  ID′ (CID Δ) {PR Δ Δ δ₀₀ δ₁₀} {PR Δ Δ δ₀₁ δ₁₁} (PR (ID Δ δ₀₀ δ₀₁) (ID Δ δ₁₀ δ₁₁) δ₀₂ δ₁₂) δ₂₀ δ₂₁

-- Given the top and bottom of a square, this "total left-right
-- identity telescope" includes a left and right plus a filler.
TSQ-LR : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁)) → Tel
TSQ-LR Δ {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ =
  TID′ (CID Δ) {PR Δ Δ δ₀₀ δ₁₀} {PR Δ Δ δ₀₁ δ₁₁} (PR (ID Δ δ₀₀ δ₀₁) (ID Δ δ₁₀ δ₁₁) δ₀₂ δ₁₂)

-- Similarly, given the left and right of a square, the "total
-- top-bottom identity telescope" includes a top and bottom plus a
-- filler.
TSQ-TB : (Δ : Tel) {δ₀₀ δ₀₁ δ₁₀ δ₁₁ : el Δ} (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) → Tel
TSQ-TB Δ {δ₀₀} {δ₀₁} {δ₁₀} {δ₁₁} δ₂₀ δ₂₁ = ID (TID Δ) (tot δ₀₀ δ₁₀ δ₂₀) (tot δ₀₁ δ₁₁ δ₂₁)

tsq-tb : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁)) →
  el (TSQ-TB Δ δ₂₀ δ₂₁)
tsq-tb Δ {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ =
  PAIR (λ w₂ → ID′ (CID Δ) w₂ δ₂₀ δ₂₁) (PR (ID Δ δ₀₀ δ₀₁) (ID Δ δ₁₀ δ₁₁) δ₀₂ δ₁₂) δ₂₂

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
         ∷ coe→ (Id-AP (λ w → left w) {tot δ₀₀ δ₁₀ δ₂₀} {tot δ₀₁ δ₁₁ δ₂₁} (tsq-tb Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) A a₀₀ a₀₁) a₀₂
         ∷ coe→ (Id-AP (λ z → right (pop z)) {tot δ₀₀ δ₁₀ δ₂₀ ∷ a₀₀} {tot δ₀₁ δ₁₁ δ₂₁ ∷ a₀₁}
                       (tsq-tb Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ ∷ coe→ (Id-AP (λ w → left w) (tsq-tb Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) A a₀₀ a₀₁) a₀₂)
                       A a₁₀ a₁₁) a₁₂

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

------------------------------
-- Symmetry
------------------------------

postulate
  SYM : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
    (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) →
    el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁) → el (SQ Δ δ₂₀ δ₂₁ δ₀₂ δ₁₂)
  SYM-SYM : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
    (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁)) →
    SYM Δ δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) ≡ δ₂₂

{-# REWRITE SYM-SYM #-}

postulate
  sym : {Δ : Tel} (A : el Δ → Type)
        {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
        (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
        {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
        (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
        Sq A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁ → Sq A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂ a₁₂
  sym-sym : {Δ : Tel} (A : el Δ → Type)
            {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
            (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
            {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
            (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) (a₂₂ : Sq A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁) →
            sym A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂ a₁₂ (sym A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂) ≡ a₂₂

{-# REWRITE sym-sym #-}

------------------------------
-- Composition and filling
------------------------------

-- The arguments to all of these operations are the same as those of Sq.

comp→ : {Δ : Tel} (A : el Δ → Type)
  {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁) (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) →
  Id′ A δ₂₁ a₀₁ a₁₁
comp→ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  tr→ {TID Δ ▸ (λ w → A (left w)) ▸ (λ w → A (right (pop w)))}
      (λ w → Id′ {Δ} A (mid {Δ} (pop (pop w))) (top (pop w)) (top w))
      {tot δ₀₀ δ₁₀ δ₂₀ ∷ a₀₀ ∷ a₁₀} {tot δ₀₁ δ₁₁ δ₂₁ ∷ a₀₁ ∷ a₁₁}
      (tsq-tb-lift Δ A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂)
      a₂₀

fill→ : {Δ : Tel} (A : el Δ → Type)
  {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁) (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) →
  Sq {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀
    (comp→ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀)
fill→ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  lift→ {TID Δ ▸ (λ w → A (left w)) ▸ (λ w → A (right (pop w)))}
      (λ w → Id′ {Δ} A (mid {Δ} (pop (pop w))) (top (pop w)) (top w))
      {tot δ₀₀ δ₁₀ δ₂₀ ∷ a₀₀ ∷ a₁₀} {tot δ₀₁ δ₁₁ δ₂₁ ∷ a₀₁ ∷ a₁₁}
      (tsq-tb-lift Δ A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂)
      a₂₀

comp← : {Δ : Tel} (A : el Δ → Type)
  {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
  Id′ A δ₂₀ a₀₀ a₁₀
comp← {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  tr← {TID Δ ▸ (λ w → A (left w)) ▸ (λ w → A (right (pop w)))}
      (λ w → Id′ {Δ} A (mid {Δ} (pop (pop w))) (top (pop w)) (top w))
      {tot δ₀₀ δ₁₀ δ₂₀ ∷ a₀₀ ∷ a₁₀} {tot δ₀₁ δ₁₁ δ₂₁ ∷ a₀₁ ∷ a₁₁}
      (tsq-tb-lift Δ A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂)
      a₂₁

fill← : {Δ : Tel} (A : el Δ → Type)
  {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
  Sq {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂
    (comp← {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁) a₂₁
fill← {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  lift← {TID Δ ▸ (λ w → A (left w)) ▸ (λ w → A (right (pop w)))}
      (λ w → Id′ {Δ} A (mid {Δ} (pop (pop w))) (top (pop w)) (top w))
      {tot δ₀₀ δ₁₀ δ₂₀ ∷ a₀₀ ∷ a₁₀} {tot δ₀₁ δ₁₁ δ₂₁ ∷ a₀₁ ∷ a₁₁}
      (tsq-tb-lift Δ A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂)
      a₂₁

-- The top-bottom fillers are then obtained from symmetry.

comp↑ : {Δ : Tel} (A : el Δ → Type)
  {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
  Id′ A δ₁₂ a₁₀ a₁₁
comp↑ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
  comp→ A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂

fill↑ : {Δ : Tel} (A : el Δ → Type)
  {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
  Sq {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} 
    (comp↑ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁) a₂₀ a₂₁
fill↑ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
  sym A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂
    (comp→ A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂)
    (fill→ A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂)

comp↓ : {Δ : Tel} (A : el Δ → Type)
  {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁) (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
  Id′ A δ₀₂ a₀₀ a₀₁
comp↓ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  comp← A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₁₂

fill↓ : {Δ : Tel} (A : el Δ → Type)
  {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁) (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
  Sq {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁}
    (comp↓ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁)
    {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁
fill↓ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  sym A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁
    (comp← A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₁₂) a₁₂
    (fill← A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₁₂)

----------------------------------------
-- Degenerate squares
----------------------------------------

{-

DEGSQ-TB : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → el (SQ Δ δ₂ δ₂ (REFL δ₀) (REFL δ₁))
DEGSQ-TB {Δ} {δ₀} {δ₁} δ₂ = {!
 -- We need an AP-PAIR!
 --TOP (λ w₂ → ID′ (λ z → ID Δ (FST Δ Δ z) (SND Δ Δ z)) w₂ (REFL δ₀) (REFL δ₁))
   --  (AP {Δ} {TID Δ} (λ w → tot w w (REFL w)) δ₂)
 !}

DEGSQ-LR : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → el (SQ Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂)
DEGSQ-LR {Δ} {δ₀} {δ₁} δ₂ = {!REFL δ₂!} -- Needs an ID-REFL (and PAIR-REFL) that we may not have proven yet.

-- Hmm, this should really be for refl of *any* variable in the telescope.
postulate
  ap-refl : {Δ : Tel} {A : el Δ → Type} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) {a₀ : A δ₀} {a₁ : A δ₁} (a₂ : Id′ A δ₂ a₀ a₁) →
    ap {Δ ▸ A} (λ w → refl (top w)) {δ₀ ∷ a₀} {δ₁ ∷ a₁} (δ₂ ∷ a₂) ≡
    {! -- First we need AP-REFL computing to a SYM for telescopes, so
      -- that the type version has something to depend on.

      -- This square telescope:
      --- SQ Δ δ₂ δ₂ (REFL δ₀) (REFL δ₁)
      -- is the type of the third component of
      --- (AP {Δ} {TID Δ} (λ w → tot w w (REFL w)) δ₂)
      -- (The first two components are δ₂; I included them because we don't have a dependent AP for telescopes.)

      -- So we should hope that the goal type can be massaged into:
      --- Sq A δ₂ δ₂ (REFL δ₀) (REFL δ₁) (mid (AP {Δ} {TID Δ} (λ w → tot w w (REFL w)) δ₂)) a₂ a₂ (refl a₀) (refl a₁)
      -- (The last two refls require some munging.)

      -- This square telescope:
      --- SQ Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂
      -- is related to the type of REFL δ₂:
      --- el (ID (ID Δ δ₀ δ₁) δ₂ δ₂)
      -- 

      -- So we should hope to be able to apply symmetry to something like this:
      --- Sq A (REFL δ₀) (REFL δ₁) δ₂ δ₂ ? (refl a₀) (refl a₁) a₂ a₂

!}

-}
