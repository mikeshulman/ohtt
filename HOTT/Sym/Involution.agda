{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Involution where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Square.Equality
open import HOTT.Sym.Base

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
  sym-sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′₀₂ A δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′₁₂ A δ a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁)
    {δ' : el (SQ Δ)} (ϕ : δ' ≡ SYM Δ δ)
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} (a₀₂' : Id′₀₂ A δ' a₀₀' a₀₁')
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} (a₁₂' : Id′₁₂ A δ' a₀₂' a₁₀' a₁₁')
    (a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀') (a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁')
    (e₀₀ : a₀₀' ≡ʰ a₀₀) (e₀₁ : a₀₁' ≡ʰ a₁₀) (e₀₂ : a₀₂' ≡ʰ a₂₀)
    (e₁₀ : a₁₀' ≡ʰ a₀₁) (e₁₁ : a₁₁' ≡ʰ a₁₁) (e₁₂ : a₁₂' ≡ʰ a₂₁)
    (e₂₀ : a₂₀' ≡ʰ a₀₂) (e₂₁ : a₂₁' ≡ʰ a₁₂)
    {δ'' : el (SQ Δ)} (ϕ' : δ'' ≡ SYM Δ δ')
    {a₀₀'' : A (δ'' ₀₀)} {a₀₁'' : A (δ'' ₀₁)} (a₀₂'' : Id′₀₂ A δ'' a₀₀'' a₀₁'')
    {a₁₀'' : A (δ'' ₁₀)} {a₁₁'' : A (δ'' ₁₁)} (a₁₂'' : Id′₁₂ A δ'' a₀₂'' a₁₀'' a₁₁'')
    (a₂₀'' : Id′ A (δ'' ₂₀) a₀₀'' a₁₀'') (a₂₁'' : Id′ A (δ'' ₂₁) a₀₁'' a₁₁'')
    (e₀₀' : a₀₀'' ≡ʰ a₀₀') (e₀₁' : a₀₁'' ≡ʰ a₁₀') (e₀₂' : a₀₂'' ≡ʰ a₂₀')
    (e₁₀' : a₁₀'' ≡ʰ a₀₁') (e₁₁' : a₁₁'' ≡ʰ a₁₁') (e₁₂' : a₁₂'' ≡ʰ a₂₁')
    (e₂₀' : a₂₀'' ≡ʰ a₀₂') (e₂₁' : a₂₁'' ≡ʰ a₁₂')
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
    sym A δ' a₀₂' a₁₂' a₂₀' a₂₁' ϕ' a₀₂'' a₁₂'' a₂₀'' a₂₁'' e₀₀' e₀₁' e₀₂' e₁₀' e₁₁' e₁₂' e₂₀' e₂₁'
      (sym A δ a₀₂ a₁₂ a₂₀ a₂₁ ϕ a₀₂' a₁₂' a₂₀' a₂₁' e₀₀ e₀₁ e₀₂ e₁₀ e₁₁ e₁₂ e₂₀ e₂₁ a₂₂) ≡
    coe← (Id′≡ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
               (sq₁₂≡ A (ϕ' • (cong (SYM Δ) ϕ) • SYM-SYM Δ δ)
                        (e₀₀' •ʰ e₀₀) (e₀₁' •ʰ e₁₀) (e₀₂' •ʰ e₂₀) (e₁₀' •ʰ e₀₁) (e₁₁' •ʰ e₁₁) (e₁₂' •ʰ e₂₁)) (e₂₀' •ʰ e₀₂) (e₂₁' •ʰ e₁₂))
         a₂₂

-- The extra freedom in sym-sym′ is also convenient when proving SYM-SYM.

-- Unfortunately, once again Agda can't normalize the type in a
-- sensible amount of time to enable us to figure out how to prove it,
-- so we just postulate it.
postulate 
  SYM-SYM▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ (Δ ▸ A))) → SYM (Δ ▸ A) (SYM (Δ ▸ A) δ) ≡ δ

SYM-SYM ε δ = reflᵉ
SYM-SYM (Δ ▸ A) δ = SYM-SYM▸ A δ
{-
  sq₂₂≡ A (SYM-SYM Δ (popsq δ))
    reflʰ
    reflʰ
    ?
    reflʰ
    reflʰ
    ?
    ?
    ?
    ?
-}

{-# REWRITE sym-sym #-}
