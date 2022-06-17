{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Fill where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Square.Boundary
open import HOTT.Sym.Base
open import HOTT.Sym.Involution

------------------------------
-- Composition and filling
------------------------------

-- Left-right and right-left fillers come from transport and lifting over squares.

-- TODO: After we start actually using fillers, we should rethink the
-- placement of the frobnications.  Currently, the inputs are ordinary
-- equalities, while the output is a square whose boundary contains
-- their frobnications and/or those of the composite.  This could be
-- best, but it might also turn out to be more useful to allow the
-- caller to specify the desired boundaries of the output along with
-- equalities to the boundaries of the input, as we did with sym.

comp→ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) →
  Id′ A (δ ₂₁) a₀₁ a₁₁
comp→ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  tr→ {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
      a₂₀

fill→ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) →
  Sq A δ (frob₀₂ A δ a₀₂) (frob₁₂ A δ a₀₂ a₁₂) a₂₀ (comp→ A δ a₀₂ a₁₂ a₂₀)
fill→ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  lift→ {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
      a₂₀

comp← : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Id′ A (δ ₂₀) a₀₀ a₁₀
comp← {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  tr← {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
      a₂₁

fill← : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ (frob₀₂ A δ a₀₂) (frob₁₂ A δ a₀₂ a₁₂) (comp← A δ a₀₂ a₁₂ a₂₁) a₂₁
fill← {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  lift← {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
      a₂₁

-- The top-bottom fillers are then obtained from symmetry.

comp↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Id′ A (δ ₁₂) a₁₀ a₁₁
comp↑ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
   coe→ (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ)
        (comp→ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
                           (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁)
                           (coe← (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) a₀₂)) 

fill↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ (frob₀₂ A δ a₀₂) (frob₁₂ A δ a₀₂ (comp↑ A δ a₀₂ a₂₀ a₂₁)) a₂₀ a₂₁
fill↑ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
   sym A (SYM Δ δ)
     -- Boundary of the input square
     (frob₀₂ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀))
     (frob₁₂ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
       (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁))
     (coe← (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) a₀₂)
     (comp→ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
       (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁)
       (coe← (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) a₀₂))
     -- Identification of the base square
     (rev (SYM-SYM Δ δ))
     -- Boundary of the output square
     (frob₀₂ A δ a₀₂)
     (frob₁₂ A δ a₀₂ (comp↑ A δ a₀₂ a₂₀ a₂₁))
     a₂₀
     a₂₁
     -- Equalities between the eight boundary components
     reflʰ
     reflʰ
     (frob₀₂≡ A δ a₀₂ •ʰ revʰ (coe←≡ʰ (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) a₀₂))
     reflʰ
     reflʰ
     (frob₁₂≡ A δ a₀₂ (comp↑ A δ a₀₂ a₂₀ a₂₁) •ʰ
      coe→≡ʰ (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ)
             (comp→ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
                                (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁)
                                (coe← (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) a₀₂)))
     (revʰ (frob₀₂≡ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀) •ʰ
            coe←≡ʰ (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀))
     (revʰ (frob₁₂≡ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀) (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁) •ʰ
            coe←≡ʰ (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁))
     -- The input square
     (fill→ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
                        (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁)
                        (coe← (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) a₀₂))
   

comp↓ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)}
  (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Id′ A (δ ₀₂) a₀₀ a₀₁
comp↓ {Δ} A δ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
   coe→ (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ)
        (comp← A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
                           (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁)
                           (coe← (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ) a₁₂))

fill↓ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)}
  (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ (frob₀₂ A δ (comp↓ A δ a₁₂ a₂₀ a₂₁)) (frob₁₂ A δ (comp↓ A δ a₁₂ a₂₀ a₂₁) a₁₂) a₂₀ a₂₁
fill↓ {Δ} A δ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
   sym A (SYM Δ δ)
     -- Boundary of the input square
     _ _ _ _
     -- Identification of the base square
     (rev (SYM-SYM Δ δ))
     -- Boundary of the output square
     (frob₀₂ A δ (comp↓ A δ a₁₂ a₂₀ a₂₁))
     (frob₁₂ A δ (comp↓ A δ a₁₂ a₂₀ a₂₁) a₁₂)
     a₂₀
     a₂₁
     -- Equalities between the eight boundary components
     reflʰ
     reflʰ
     (frob₀₂≡ A δ (comp↓ A δ a₁₂ a₂₀ a₂₁) •ʰ
      coe→≡ʰ (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ)
             (comp← A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
                                (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁)
                                (coe← (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ) a₁₂)))
     reflʰ
     reflʰ
     (frob₁₂≡ A δ (comp↓ A δ a₁₂ a₂₀ a₂₁) a₁₂ •ʰ revʰ (coe←≡ʰ (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ) a₁₂))
     (revʰ (frob₀₂≡ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀) •ʰ
            coe←≡ʰ (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀))
     (revʰ (frob₁₂≡ A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀) (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁) •ʰ
            coe←≡ʰ (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁))
     -- The input square
     (fill← A (SYM Δ δ) (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
                        (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁)
                        (coe← (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ) a₁₂))
