{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Involution where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Square.Top
open import HOTT.Sym.Base

-- TODO: Move these to Square.Base

sqbase≡ : {Δ : Tel} (A : el Δ → Type) {δ δ' : el (SQ Δ)} (ϕ : δ ≡ δ')
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} {a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁}
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} {a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁}
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} {a₀₂' : Id′ A (δ' ₀₂) a₀₀' a₀₁'}
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} {a₁₂' : Id′ A (δ' ₁₂) a₁₀' a₁₁'}
    (e₀₀ : a₀₀ ≡ʰ a₀₀') (e₀₁ : a₀₁ ≡ʰ a₀₁') (e₀₂ : a₀₂ ≡ʰ a₀₂')
    (e₁₀ : a₁₀ ≡ʰ a₁₀') (e₁₁ : a₁₁ ≡ʰ a₁₁') (e₁₂ : a₁₂ ≡ʰ a₁₂')
  → _≡_
    {el (ID (ID Δ)
    ▸ (λ x → A (x ₀₀))
    ▸ (λ x → A ((pop x) ₀₁))
    ▸ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
    ▸ (λ x → A ((pop (pop (pop x))) ₁₀))
    ▸ (λ x → A ((pop (pop (pop (pop x)))) ₁₁))
    ▸ (λ x → Id′ (λ y → A ((pop y) ₁)) (pop (pop x)) (top (pop x)) (top x)))}
    (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
    (δ' ∷ a₀₀' ∷ a₀₁' ∷ frob₀₂ A δ' a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ frob₁₂ A δ' a₀₂' a₁₂')
sqbase≡ A reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ = reflᵉ

sq∷≡ : {Δ : Tel} (A : el Δ → Type) {δ δ' : el (SQ Δ)} (ϕ : δ ≡ δ')
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} {a₀₂ : Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁}
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} {a₁₂ : Id′ (λ w → A (pop w ₁)) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) a₁₀ a₁₁}
    {a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀} {a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁}
    {a₂₂ : Id′ -- {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A ((pop x) ₁))}
      (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂) a₂₀ a₂₁}
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} {a₀₂' : Id′ (λ x → A (x ₀)) δ' a₀₀' a₀₁'}
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} {a₁₂' : Id′ (λ w → A (pop w ₁)) (δ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂') a₁₀' a₁₁'}
    {a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀'} {a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁'}
    {a₂₂' : Id′ -- {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A ((pop x) ₁))}
      (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (δ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ a₁₂') a₂₀' a₂₁'}
    (e₀₀ : a₀₀ ≡ʰ a₀₀') (e₀₁ : a₀₁ ≡ʰ a₀₁') (e₀₂ : a₀₂ ≡ʰ a₀₂')
    (e₁₀ : a₁₀ ≡ʰ a₁₀') (e₁₁ : a₁₁ ≡ʰ a₁₁') (e₁₂ : a₁₂ ≡ʰ a₁₂')
    (e₂₀ : a₂₀ ≡ʰ a₂₀') (e₂₁ : a₂₁ ≡ʰ a₂₁') (e₂₂ : a₂₂ ≡ʰ a₂₂')
  → _≡_
    {el (ID (ID Δ)
    ▸ (λ x → A (x ₀₀))
    ▸ (λ x → A ((pop x) ₀₁))
    ▸ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
    ▸ (λ x → A ((pop (pop (pop x))) ₁₀))
    ▸ (λ x → A ((pop (pop (pop (pop x)))) ₁₁))
    ▸ (λ x → Id′ (λ y → A ((pop y) ₁)) (pop (pop x)) (top (pop x)) (top x))
    ▸ (λ x → Id′ A (pop (pop (pop (pop (pop (pop x))))) ₀) (top (pop (pop (pop (pop (pop x)))))) (top (pop (pop x))))
    ▸ (λ x → Id′ A (pop (pop (pop (pop (pop (pop (pop x)))))) ₁) (top (pop (pop (pop (pop (pop x)))))) (top (pop (pop x))))
    ▸ (λ x → Id′ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) (pop (pop x)) (top (pop x)) (top x)))}
    (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂)
    (δ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ a₁₂' ∷ a₂₀' ∷ a₂₁' ∷ a₂₂')
sq∷≡ A reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ = reflᵉ

------------------------------
-- Symmetry is an involution
------------------------------

-- We postulate that symmetry on types is an involution, and mutually
-- prove from this that it is an involution on telescopes.

SYM-SYM : (Δ : Tel) (δ : el (SQ Δ)) → SYM Δ (SYM Δ δ) ≡ δ

-- We would like to declare symmetry on types as a rewrite.  (Symmetry
-- on telescopes doesn't make as much sense as a rewrite, since it
-- involves coercions along the equalities SYMₘₙ that aren't rewrites,
-- but having symmetry on types be a rewrite should imply that
-- symmetry on concrete telescopes also rewrites.)  Unfortunately, the
-- naive postulate that would look something like
---
--- sym-sym : ... → sym A (SYM Δ δ) ... (sym A δ ... a₂₂) ≡ a₂₂
---
-- isn't suitable as a rewrite, because it has the volatile SYM on the
-- left.  When Δ is concrete, this SYM will reduce, and Agda won't be
-- able to un-reduce it to notice that the two sym's match.  This is
-- the main reason for postulating instead the enhanced symmetry sym′,
-- that incorporates coercion across equalities.  It allows us to
-- formulate sym-sym′, below, whose LHS is not volatile and can
-- hopefully be pattern-matched so that the rewrite will fire.

postulate
  sym-sym′ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
    (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁)
    {δ' : el (SQ Δ)} (ϕ : δ' ≡ SYM Δ δ)
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} (a₀₂' : Id′ A (δ' ₀₂) a₀₀' a₀₁')
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} (a₁₂' : Id′ A (δ' ₁₂) a₁₀' a₁₁')
    (a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀') (a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁')
    (e₀₀ : a₀₀' ≡ʰ a₀₀) (e₀₁ : a₀₁' ≡ʰ a₁₀) (e₀₂ : a₀₂' ≡ʰ a₂₀)
    (e₁₀ : a₁₀' ≡ʰ a₀₁) (e₁₁ : a₁₁' ≡ʰ a₁₁) (e₁₂ : a₁₂' ≡ʰ a₂₁)
    (e₂₀ : a₂₀' ≡ʰ a₀₂) (e₂₁ : a₂₁' ≡ʰ a₁₂)
    {δ'' : el (SQ Δ)} (ϕ' : δ'' ≡ SYM Δ δ')
    {a₀₀'' : A (δ'' ₀₀)} {a₀₁'' : A (δ'' ₀₁)} (a₀₂'' : Id′ A (δ'' ₀₂) a₀₀'' a₀₁'')
    {a₁₀'' : A (δ'' ₁₀)} {a₁₁'' : A (δ'' ₁₁)} (a₁₂'' : Id′ A (δ'' ₁₂) a₁₀'' a₁₁'')
    (a₂₀'' : Id′ A (δ'' ₂₀) a₀₀'' a₁₀'') (a₂₁'' : Id′ A (δ'' ₂₁) a₀₁'' a₁₁'')
    (e₀₀' : a₀₀'' ≡ʰ a₀₀') (e₀₁' : a₀₁'' ≡ʰ a₁₀') (e₀₂' : a₀₂'' ≡ʰ a₂₀')
    (e₁₀' : a₁₀'' ≡ʰ a₀₁') (e₁₁' : a₁₁'' ≡ʰ a₁₁') (e₁₂' : a₁₂'' ≡ʰ a₂₁')
    (e₂₀' : a₂₀'' ≡ʰ a₀₂') (e₂₁' : a₂₁'' ≡ʰ a₁₂')
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
    sym′ A δ' a₀₂' a₁₂' a₂₀' a₂₁' ϕ' a₀₂'' a₁₂'' a₂₀'' a₂₁'' e₀₀' e₀₁' e₀₂' e₁₀' e₁₁' e₁₂' e₂₀' e₂₁'
      (sym′ A δ a₀₂ a₁₂ a₂₀ a₂₁ ϕ a₀₂' a₁₂' a₂₀' a₂₁' e₀₀ e₀₁ e₀₂ e₁₀ e₁₁ e₁₂ e₂₀ e₂₁ a₂₂) ≡
    coe← (Id′≡ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
           (sqbase≡ A (ϕ' • (cong (SYM Δ) ϕ) • SYM-SYM Δ δ)
             (e₀₀' •ʰ e₀₀) (e₀₁' •ʰ e₁₀) (e₀₂' •ʰ e₂₀) (e₁₀' •ʰ e₀₁) (e₁₁' •ʰ e₁₁) (e₁₂' •ʰ e₂₁))
           (e₂₀' •ʰ e₀₂) (e₂₁' •ʰ e₁₂))
         a₂₂

-- The extra freedom in sym-sym′ is also convenient when proving SYM-SYM.

SYM-SYM ε δ = reflᵉ
SYM-SYM (Δ ▸ A) δ =
  {!sq∷≡ A (SYM-SYM Δ (popsq δ))
    ?
    ?
    ?
    ?
    ?
    ?
    ?
    ?
    ? !}

{-
sq∷ A
      (SYM Δ
       (popsq
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (coe←
       (Id′≡ A
        (SYM₀₂
         (popsq
          (sq∷ A (SYM Δ (popsq δ))
           (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
           (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
           (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
           (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
           (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
            (top₂₂ δ)))))
        reflʰ reflʰ)
       (top₂₀
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (coe←
       (Id′≡ A
        (SYM₁₂
         (popsq
          (sq∷ A (SYM Δ (popsq δ))
           (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
           (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
           (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
           (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
           (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
            (top₂₂ δ)))))
        reflʰ reflʰ)
       (top₂₁
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (coe←
       (Id′≡ A
        (SYM₂₀
         (popsq
          (sq∷ A (SYM Δ (popsq δ))
           (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
           (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
           (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
           (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
           (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
            (top₂₂ δ)))))
        reflʰ reflʰ)
       (top₀₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (coe←
       (Id′≡ A
        (SYM₂₁
         (popsq
          (sq∷ A (SYM Δ (popsq δ))
           (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
           (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
           (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
           (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
           (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
            (top₂₂ δ)))))
        reflʰ reflʰ)
       (top₁₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (sym A
       (popsq
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₀₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₁₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₂₀
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₂₁
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₂₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      ≡ δ
-}

-- {-# REWRITE sym-sym′ #-}
