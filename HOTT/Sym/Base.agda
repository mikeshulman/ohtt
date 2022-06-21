{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Square.Equality

------------------------------
-- Symmetry
------------------------------

-- Symmetry for telescopes will be defined in terms of symmetry for types.
postulate
  SYM : (Δ : Tel) → el (SQ Δ) → el (SQ Δ)
  SYM-SYM : (Δ : Tel) (δ : el (SQ Δ)) → SYM Δ (SYM Δ δ) ≡ δ

{-# REWRITE SYM-SYM #-}
  
-- We also have to define it mutually with proofs that it transposes
-- the boundary.  We expand out the left-hand sides of those that will
-- be rewrites, since rewriting requires the LHS to not be a redex.
postulate
  SYM₀₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₀ ≡ δ ₀₀
  SYM₀₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₀ ≡ δ ₁₀
  SYM₁₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₁ ≡ δ ₀₁
  SYM₁₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₁ ≡ δ ₁₁
  SYM₀₂ : {Δ : Tel} (δ : el (SQ Δ)) → AP _₀ (SYM Δ δ) ≡ δ ₂₀
  SYM₁₂ : {Δ : Tel} (δ : el (SQ Δ)) → AP _₁ (SYM Δ δ) ≡ δ ₂₁
  SYM₂₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ≡ δ ₀₂
  SYM₂₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ≡ δ ₁₂

{-# REWRITE SYM₀₀ SYM₀₁ SYM₁₀ SYM₁₁ SYM₀₂ SYM₂₀ SYM₁₂ SYM₂₁ #-}

postulate
  Id′-AP-₂₀-SYM : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) {a₀₀ : A (δ ₀₀)} {a₁₀ : A (δ ₁₀)} →
    Id′ A (δ ₂₀) a₀₀ a₁₀ ≡ Id′ (λ x → A (x ₀)) (SYM Δ δ) a₀₀ a₁₀
  Id′-AP-₂₁-SYM : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) {a₀₁ : A (δ ₀₁)} {a₁₁ : A (δ ₁₁)} →
    Id′ A (δ ₂₁) a₀₁ a₁₁ ≡ Id′ (λ x → A (x ₁)) (SYM Δ δ) a₀₁ a₁₁

{-# REWRITE Id′-AP-₂₀-SYM Id′-AP-₂₁-SYM #-}

-- Symmetry for types, of course, is a postulated operation, which
-- takes a square over δ to a square over (SYM Δ δ).  It also
-- transposes the boundary, and moreover must coerce the boundary
-- across the above proofs that SYM transposes the boundary.
postulate
  sym′ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′₀₂ A δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′₁₂ A δ a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
    {δ' : el (SQ Δ)} (ϕ : δ' ≡ SYM Δ δ)
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} (a₀₂' : Id′₀₂ A δ' a₀₀' a₀₁')
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} (a₁₂' : Id′₁₂ A δ' a₀₂' a₁₀' a₁₁')
    (a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀') (a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁') →
    (a₀₀' ≡ʰ a₀₀) → (a₀₁' ≡ʰ a₁₀) → (a₀₂' ≡ʰ a₂₀) →
    (a₁₀' ≡ʰ a₀₁) → (a₁₁' ≡ʰ a₁₁) → (a₁₂' ≡ʰ a₂₁) →
    (a₂₀' ≡ʰ a₀₂) → (a₂₁' ≡ʰ a₁₂) →
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
    Sq A δ' {a₀₀'} {a₀₁'} a₀₂' {a₁₀'} {a₁₁'} a₁₂' a₂₀' a₂₁'

sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′₀₂ A δ a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′₁₂ A δ a₀₂ a₁₀ a₁₁)
  (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁)
  (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
  Sq A (SYM Δ δ) {a₀₀} {a₁₀} a₂₀
  {a₀₁} {a₁₁} (Id′-pop→ (λ x → A (x ₁)) (λ w → A (w ₀)) (SYM Δ δ) a₂₀ a₂₁)
  a₀₂ (Id′-pop← (λ x → A (x ₁)) (λ w → A (w ₀)) δ a₀₂ a₁₂)
sym {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ a₂₂ =
  sym′ A δ a₀₂ a₁₂ a₂₀ a₂₁ reflᵉ
    a₂₀ (Id′-pop→ (λ x → A (x ₁)) (λ w → A (w ₀)) (SYM Δ δ) a₂₀ a₂₁) a₀₂ (Id′-pop← (λ x → A (x ₁)) (λ w → A (w ₀)) δ a₀₂ a₁₂)
    reflʰ reflʰ reflʰ reflʰ reflʰ (Id′-pop→≡ (λ x → A (x ₁)) (λ w → A (w ₀)) (SYM Δ δ) a₂₀ a₂₁)
    reflʰ (Id′-pop←≡ (λ x → A (x ₁)) (λ w → A (w ₀)) δ a₀₂ a₁₂)
    a₂₂ 

-- Now we can define symmetry for telescopes by decomposing a collated
-- SQ, transposing and applying symmetry, and recomposing again.
postulate
  SYMε : (δ : el (SQ ε)) → SYM ε δ ≡ []
  SYM▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′₀₂ A δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′₁₂ A δ a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
      SYM (Δ ▸ A) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) ≡
        SYM Δ δ
        ∷ a₀₀ ∷ a₁₀ ∷ a₂₀
        ∷ a₀₁ ∷ a₁₁ ∷ (Id′-pop→ (λ x → A (x ₁)) (λ w → A (w ₀)) (SYM Δ δ) a₂₀ a₂₁)
        ∷ a₀₂ ∷ (Id′-pop← (λ x → A (x ₁)) (λ w → A (w ₀)) δ a₀₂ a₁₂)
        ∷ sym A δ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂

{-# REWRITE SYMε SYM▸ #-}

-- We would like to declare the fact that symmetry on types is an
-- involution as a rewrite.  Unfortunately, the naive postulate that
-- would look something like
---
--- sym-sym : ... → sym A (SYM Δ δ) ... (sym A δ ... a₂₂) ≡ a₂₂
---
-- isn't very suitable as a rewrite, because it has the volatile SYM
-- on the left.  When Δ is concrete, this SYM will reduce, and Agda
-- won't be able to un-reduce it to notice that the two sym's match.
-- This is the main reason for postulating instead the enhanced
-- symmetry sym′, that incorporates coercion across equalities.  It
-- allows us to formulate sym-sym′, below, whose LHS is not volatile
-- and can hopefully be pattern-matched so that the rewrite will fire.

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
    sym′ A δ' a₀₂' a₁₂' a₂₀' a₂₁' ϕ' a₀₂'' a₁₂'' a₂₀'' a₂₁'' e₀₀' e₀₁' e₀₂' e₁₀' e₁₁' e₁₂' e₂₀' e₂₁'
      (sym′ A δ a₀₂ a₁₂ a₂₀ a₂₁ ϕ a₀₂' a₁₂' a₂₀' a₂₁' e₀₀ e₀₁ e₀₂ e₁₀ e₁₁ e₁₂ e₂₀ e₂₁ a₂₂) ≡
    coe← (Sq≡ A (ϕ' • (cong (SYM Δ) ϕ)) (e₀₀' •ʰ e₀₀) (e₀₁' •ʰ e₁₀) (e₀₂' •ʰ e₂₀) (e₁₀' •ʰ e₀₁) (e₁₁' •ʰ e₁₁) (e₁₂' •ʰ e₂₁) (e₂₀' •ʰ e₀₂) (e₂₁' •ʰ e₁₂)) a₂₂
