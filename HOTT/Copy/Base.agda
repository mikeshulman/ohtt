{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K  #-}

module HOTT.Copy.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl

------------------------------
-- Copy-types
------------------------------

infixl 50 _↑
infixl 50 _↓

-- (Copy A) is like a coinductive type with one destructor _↓ valued
-- in A.  Thus, it also has a constructor _↑ with inputs from A, with
-- a β-rule but no η-rule.

data Copy (A : Type) : Type where
  _↑ : A → Copy A
  
-- Apparently this isn't projection-like, so we don't need --no-projection-like
_↓ : {A : Type} → Copy A → A
a ↑ ↓ = a

postulate
  Id-Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : Copy (A (δ ₀))) (a₁ : Copy (A (δ ₁))) →
    Id (Λ w ⇨ Copy (A w)) δ a₀ a₁ ≡ Copy (Id (Λ⇨ A) δ (a₀ ↓) (a₁ ↓))
  ＝-Copy : (A : Type) (a₀ a₁ : Copy A) →
    (a₀ ＝ a₁) ≡ Copy ((a₀ ↓ ＝ a₁ ↓))

{-# REWRITE Id-Copy ＝-Copy #-}

-- Since (Copy A) has no η-rule, it's not reasonable to compute ap and
-- refl directly on its constructor _↑.  Instead they should compute
-- only after the destructor _↓ has been applied (a "copattern
-- match").  To implement this with rewrite rules, we introduce a new
-- version of _↑ that remembers "the type it came from", which behaves
-- just like _↑ as far as the destructor is concerned, but can't be
-- identified definitionally with _↑ or with other instances of _⇑.

postulate
  _⇑ : {T : Typeᵉ} {t : T} {A : Type} (a : A) → Copy A
  ⇑↓ : {A : Type} (a : A) {T : Typeᵉ} (t : T) → (_⇑ {T} {t} {A} a) ↓ ≡ a
  -- We also include a "dimension-increasing" operator on the parameter types T.
  ↿ : Typeᵉ → Typeᵉ
  ↾ : {T : Typeᵉ} → T → ↿ T

infixl 30 _⇑

{-# REWRITE ⇑↓ #-}

postulate
  -- Computing ap and refl on _↓ is straightforward.
  ap↓ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a : (w : el Δ) → Copy (A w)) →
    ap (Λ⇨ A) (λ w → (a w) ↓) δ ≡ (ap (Λ w ⇨ Copy (A w))a δ) ↓
  refl↓ : {A : Type} (a : Copy A) → refl (a ↓) ≡ refl a ↓
  -- Computing them on _↑ is similar, but we parametrize the result.
  ap↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a : (w : el Δ) → A w) →
    ap (Λ w ⇨ Copy (A w)) (λ w → (a w) ↑) δ ≡ _⇑ {(w : el Δ) → A w} {a} (ap (Λ⇨ A) a δ)
  refl↑ : {A : Type} (a : A) → refl (a ↑) ≡ _⇑ {⊤ᵉ → A} {λ _ → a} (refl a)
  -- And of course we also have to compute them on _⇑.  In this case
  -- we apply the dimension-increasing operator, to make sure the
  -- results are definitionally unique.
  ap⇑ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ))
    {T : el Δ → Typeᵉ} {t : (w : el Δ) → T w} (a : (w : el Δ) → A w) →
    ap (Λ w ⇨ Copy (A w)) (λ w → _⇑ {T w} {t w} (a w)) δ ≡ _⇑ {↿ ((w : el Δ) → T w)} {↾ t} (ap (Λ⇨ A) a δ)
  refl⇑ : {T : Typeᵉ} {t : T} {A : Type} (a : A) → refl (_⇑ {T} {t} a) ≡ _⇑ {↿ T} {↾ t} (refl a)

{-# REWRITE ap↓ refl↓ ap↑ ap⇑ refl↑ refl⇑ #-}
