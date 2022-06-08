{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Universe where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Transport
open import HOTT.Prod
open import HOTT.Sigma
open import HOTT.Pi
open import HOTT.Arrow

--------------------------------------------------
-- Contractibility and 1-1 correspondences
--------------------------------------------------

isProp : (A : Type) → Type
isProp A = Π A (λ a₀ → Π A (λ a₁ → Id A a₀ a₁))

isContr : (A : Type) → Type
isContr A = A × isProp A

is11 : {A B : Type} (R : A ⇒ B ⇒ Type) → Type
is11 {A} {B} R = Π A (λ a → isContr (Σ B (λ b → R ∙ a ∙ b))) × Π B (λ b → isContr (Σ A (λ a → R ∙ a ∙ b)))

11Corr : Type → Type → Type
11Corr A B = Σ (A ⇒ B ⇒ Type) is11

------------------------------
-- Copy-types
------------------------------

infixl 30 _↑
infixl 30 _↓

postulate
  Copy : Type → Type
  _↑ : {A : Type} → A → Copy A
  _↓ : {A : Type} → Copy A → A
  ↑↓ : {A : Type} (a : A) → a ↑ ↓ ≡ a

{-# REWRITE ↑↓ #-}

postulate
  Id-Copy : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : Copy (A δ₀)) (a₁ : Copy (A δ₁)) →
    Id′ (λ w → Copy (A w)) δ₂ a₀ a₁ ≡ Copy (Id′ A δ₂ (a₀ ↓) (a₁ ↓))

{-# REWRITE Id-Copy #-}

postulate
  ap↑ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a : (w : el Δ) → A w) →
    ap (λ w → (a w) ↑) δ₂ ≡ (ap a δ₂) ↑
  ap↓ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a : (w : el Δ) → Copy (A w)) →
    ap (λ w → (a w) ↓) δ₂ ≡ (ap a δ₂) ↓

{-# REWRITE ap↑ ap↓ #-}

------------------------------
-- The universe
------------------------------

postulate
  IdU : (A B : Type) → Id Type A B ≡ Copy (11Corr A B)

{-# REWRITE IdU #-}

--- In Agda <2.6.3, apU with Copy-types leads to an internal error.
-- postulate
  -- uncopy : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) {A B : Type} →
  --   Id′ {Δ} (λ _ → Type) δ₂ A B → 11Corr A B
  -- copy : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) {A B : Type} →
  --   11Corr A B → Id′ {Δ} (λ _ → Type) δ₂ A B
  -- uncopy-copy : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) {A B : Type} (E : 11Corr A B) →
  --   uncopy Δ δ₂ (copy Δ δ₂ E) ≡ E

postulate
  apU : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    (ap A δ₂) ↓ ≡
    ((Λ a₀ ⇒ Λ a₁ ⇒ Id′ A δ₂ a₀ a₁) ﹐
    ((Λ a₀ ⇛ (tr→ A δ₂ a₀ ﹐ lift→ A δ₂ a₀ ,
              Λ x ⇛ Λ x' ⇛ utr→ A δ₂ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift→ A δ₂ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x'))) ,
     (Λ a₁ ⇛ (tr← A δ₂ a₁ ﹐ lift← A δ₂ a₁ ,
              Λ x ⇛ Λ x' ⇛ utr← A δ₂ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift← A δ₂ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x')))))

{-# REWRITE apU #-}
