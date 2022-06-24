{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Fill where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Sym.Base

----------------------------------------
-- Left-right composition and filling
----------------------------------------

-- Left-right and right-left fillers come from transport and lifting over squares.

comp→ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) →
  Id A (δ ₂₁) a₀₁ a₁₁
comp→ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  tr→ {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂)
      a₂₀

fill→ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) →
  Sq A δ a₀₂ (Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂) a₂₀ (comp→ A δ a₀₂ a₁₂ a₂₀)
fill→ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  lift→ {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂)
      a₂₀

comp← : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
  Id A (δ ₂₀) a₀₀ a₁₀
comp← {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  tr← {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂)
      a₂₁

fill← : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ a₀₂ (Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂) (comp← A δ a₀₂ a₁₂ a₂₁) a₂₁
fill← {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  lift← {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂)
      a₂₁

----------------------------------------
-- Top-bottom composition and filling
----------------------------------------

-- The top-bottom fillers are then obtained from symmetry.

comp↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
  Id A (δ ₁₂) a₁₀ a₁₁
comp↑ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ = comp→ A (SYM Δ δ) a₂₀ a₂₁ a₀₂

fill↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ a₀₂ (Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ (comp↑ A δ a₀₂ a₂₀ a₂₁)) a₂₀ a₂₁
fill↑ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
   sym A (SYM Δ δ)
     {a₀₀} {a₁₀} a₂₀
     {a₀₁} {a₁₁} (Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) (SYM Δ δ) a₂₀ a₂₁)
     a₀₂
     (comp→ A (SYM Δ δ) a₂₀ a₂₁ a₀₂)
     (fill→ A (SYM Δ δ) a₂₀ a₂₁ a₀₂)

comp↓ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)}
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁)
  (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
  Id A (δ ₀₂) a₀₀ a₀₁
comp↓ {Δ} A δ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ = comp← A (SYM Δ δ) a₂₀ a₂₁ a₁₂

fill↓ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)}
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁)
  (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ (comp↓ A δ a₁₂ a₂₀ a₂₁) (Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} (comp↓ A δ a₁₂ a₂₀ a₂₁) a₁₂) a₂₀ a₂₁
fill↓ {Δ} A δ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
   sym A (SYM Δ δ)
     {a₀₀} {a₁₀} a₂₀
     {a₀₁} {a₁₁} (Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) (SYM Δ δ) a₂₀ a₂₁)
     (comp← A (SYM Δ δ) a₂₀ a₂₁ a₁₂)
     a₁₂
     (fill← A (SYM Δ δ) a₂₀ a₂₁ a₁₂)

------------------------------
-- utr/ulift versus filling
------------------------------

-- The "2-simplex" produced by ulift can be regarded as a square.

ulift→sq : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀))
    (a₁ a₁' : A (δ ₁)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀ a₁') →
    Sq A (DEGSQ-LR δ)
      (refl a₀) (Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) (DEGSQ-LR δ) (refl a₀) (utr→ A δ a₀ a₁ a₁' a₂ a₂'))
      a₂ a₂'
ulift→sq {Δ} A δ a₀ a₁ a₁' a₂ a₂' =
  coe← (Id-AP {ε ▸ (λ _ → A (δ ₁))} {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A (pop x ₁))} (λ x → δ ∷ a₀ ∷ top x)
                 ([] ∷ a₁ ∷ a₁' ∷ utr→ A δ a₀ a₁ a₁' a₂ a₂') (λ y → Id A (pop (pop y)) (top (pop y)) (top y)) a₂ a₂')
        (ulift→ A δ a₀ a₁ a₁' a₂ a₂')

ulift←sq : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : A (δ ₁))
    (a₀ a₀' : A (δ ₀)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀' a₁) →
    Sq A (DEGSQ-LR δ)
      (utr← A δ a₁ a₀ a₀' a₂ a₂') (Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) (DEGSQ-LR δ) (utr← A δ a₁ a₀ a₀' a₂ a₂') (refl a₁))
      a₂ a₂'
ulift←sq {Δ} A δ a₁ a₀ a₀' a₂ a₂' =
  coe← (Id-AP {ε ▸ (λ _ → A (δ ₀))} {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A (pop x ₁))} (λ x → δ ∷ top x ∷ a₁)
                 ([] ∷ a₀ ∷ a₀' ∷ utr← A δ a₁ a₀ a₀' a₂ a₂') (λ y → Id A (pop (pop y)) (top (pop y)) (top y)) a₂ a₂')
        (ulift← A δ a₁ a₀ a₀' a₂ a₂')

-- Conversely, we can construct operations having the type of utr and
-- ulift from filling.  We include utr and ulift explicitly so that ↓
-- on Id-U can extract precisely the ones that were put in by ↑, but
-- when computing utr and ulift for type formers like Σ and Π it is
-- almost always easier to derive them in this way.

fill-utr→ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀))
    (a₁ a₁' : A (δ ₁)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀ a₁') → (a₁ ＝ a₁')
fill-utr→ A δ a₀ a₁ a₁' a₂ a₂' = comp↑ A (DEGSQ-LR δ) (refl a₀) a₂ a₂'

fill-ulift→ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀))
    (a₁ a₁' : A (δ ₁)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀ a₁') →
    Id {ε ▸ (λ _ → A (δ ₁))} (λ w → Id A δ a₀ (top w)) ([] ∷ a₁ ∷ a₁' ∷ fill-utr→ A δ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
fill-ulift→ {Δ} A δ a₀ a₁ a₁' a₂ a₂' =
   coe→ (Id-AP {ε ▸ (λ _ → A (δ ₁))} {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A (pop x ₁))}
           (λ x → δ ∷ a₀ ∷ top x) ([] ∷ a₁ ∷ a₁' ∷ fill-utr→ A δ a₀ a₁ a₁' a₂ a₂')
           (λ x → Id A (pop (pop x)) (top (pop x)) (top x)) a₂ a₂')
        (fill↑ A (DEGSQ-LR δ) (refl a₀) a₂ a₂')
    
fill-utr← : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : A (δ ₁))
    (a₀ a₀' : A (δ ₀)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀' a₁) → (a₀ ＝ a₀')
fill-utr← A δ a₁ a₀ a₀' a₂ a₂' = comp↓ A (DEGSQ-LR δ) (refl a₁) a₂ a₂'

fill-ulift← : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : A (δ ₁))
    (a₀ a₀' : A (δ ₀)) (a₂ : Id A δ a₀ a₁) (a₂' : Id A δ a₀' a₁) →
    Id {ε ▸ (λ _ → A (δ ₀))} (λ w → Id A δ (top w) a₁) ([] ∷ a₀ ∷ a₀' ∷ fill-utr← A δ a₁ a₀ a₀' a₂ a₂') a₂ a₂'
fill-ulift← {Δ} A δ a₁ a₀ a₀' a₂ a₂' =
   coe→ (Id-AP {ε ▸ (λ _ → A (δ ₀))} {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A (pop x ₁))}
           (λ x → δ ∷ top x ∷ a₁) ([] ∷ a₀ ∷ a₀' ∷ fill-utr← A δ a₁ a₀ a₀' a₂ a₂')
           (λ x → Id A (pop (pop x)) (top (pop x)) (top x)) a₂ a₂')
        (fill↓ A (DEGSQ-LR δ) (refl a₁) a₂ a₂')
