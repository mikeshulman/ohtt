{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Naturality where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Sym.Base

------------------------------
-- Naturality of symmetry
------------------------------

postulate
  SYM-AP-AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (SQ Γ)) →
    SYM Δ (AP (AP f) γ) ≡ AP (AP f) (SYM Γ γ)

{-# REWRITE SYM-AP-AP #-}

-- Let's do the version without added equalities, at least first.
postulate
  sym-AP : {Γ Δ : Tel} (f : el Γ → el Δ) (A : el Δ → Type) (γ : el (SQ Γ))
    {a₀₀ : A (f (γ ₀₀))} {a₀₁ : A (f (γ ₀₁))} (a₀₂ : Id′₀₂ A (AP (AP f) γ) a₀₀ a₀₁)
    {a₁₀ : A (f (γ ₁₀))} {a₁₁ : A (f (γ ₁₁))} (a₁₂ : Id′₁₂ A (AP (AP f) γ) a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id′ (λ x → A (f x)) (γ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ (λ x → A (f x)) (γ ₂₁) a₀₁ a₁₁)
    (a₂₂ : Sq A (AP (AP f) γ) a₀₂ a₁₂ a₂₀ a₂₁) →
    sym A (AP (AP f) γ) a₀₂ a₁₂ a₂₀ a₂₁ a₂₂ ≡
    {! sym (λ x → A (f x)) γ a₀₂ ? a₂₀ a₂₁ ? !}

-- {-# REWRITE sym-AP #-}

{-
postulate
  sym′-AP : {Γ Δ : Tel} (f : el Γ → el Δ) (A : el Δ → Type) (γ : el (SQ Γ))
    {a₀₀ : A (f (γ ₀₀))} {a₀₁ : A (f (γ ₀₁))} (a₀₂ : Id′₀₂ (λ x → A (f x)) γ a₀₀ a₀₁)
    {a₁₀ : A (f (γ ₁₀))} {a₁₁ : A (f (γ ₁₁))} (a₁₂ : Id′₁₂ (λ x → A (f x)) γ a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id′ (λ x → A (f x)) (γ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ (λ x → A (f x)) (γ ₂₁) a₀₁ a₁₁) →
    {γ' : el (SQ Γ)} (ϕ : γ' ≡ SYM Γ γ)
    {a₀₀' : A (f (γ' ₀₀))} {a₀₁' : A (f (γ' ₀₁))} (a₀₂' : Id′₀₂ (λ x → A (f x)) γ' a₀₀' a₀₁')
    {a₁₀' : A (f (γ' ₁₀))} {a₁₁' : A (f (γ' ₁₁))} (a₁₂' : Id′₁₂ (λ x → A (f x)) γ' a₀₂' a₁₀' a₁₁')
    (a₂₀' : Id′ (λ x → A (f x)) (γ' ₂₀) a₀₀' a₁₀') (a₂₁' : Id′ (λ x → A (f x)) (γ' ₂₁) a₀₁' a₁₁')
    (e₀₀ : a₀₀' ≡ʰ a₀₀) (e₀₁ : a₀₁' ≡ʰ a₁₀) (e₀₂ : a₀₂' ≡ʰ a₂₀)
    (e₁₀ : a₁₀' ≡ʰ a₀₁) (e₁₁ : a₁₁' ≡ʰ a₁₁) (e₁₂ : a₁₂' ≡ʰ a₂₁)
    (e₂₀ : a₂₀' ≡ʰ a₀₂) (e₂₁ : a₂₁' ≡ʰ a₁₂)
    (a₂₂ : Sq (λ x → A (f x)) γ a₀₂ a₁₂ a₂₀ a₂₁)
    {b₀₀ : A (f (γ ₀₀))} {b₀₁ : A (f (γ ₀₁))} (b₀₂ : Id′₀₂ A (AP (AP f) γ) b₀₀ b₀₁)
    {b₁₀ : A (f (γ ₁₀))} {b₁₁ : A (f (γ ₁₁))} (b₁₂ : Id′₁₂ A (AP (AP f) γ) b₀₂ b₁₀ b₁₁)
    (b₂₀ : Id′ A (AP f (γ ₂₀)) b₀₀ b₁₀) (b₂₁ : Id′ A (AP f (γ ₂₁)) b₀₁ b₁₁)
    (b₂₂ : Sq A (AP (AP f) γ) b₀₂ b₁₂ b₂₀ b₂₁)
    -- A ϕ' can be constructed as (cong (AP (AP f)) ϕ • SYM-AP f γ).
    (ϕ' : AP (AP f) γ' ≡ SYM Δ (AP (AP f) γ))
    {b₀₀' : A (f (γ' ₀₀))} {b₀₁' : A (f (γ' ₀₁))} (b₀₂' : Id′₀₂ A (AP (AP f) γ') b₀₀' b₀₁')
    {b₁₀' : A (f (γ' ₁₀))} {b₁₁' : A (f (γ' ₁₁))} (b₁₂' : Id′₁₂ A (AP (AP f) γ') b₀₂' b₁₀' b₁₁')
    (b₂₀' : Id′ A (AP f (γ' ₂₀)) b₀₀' b₁₀') (b₂₁' : Id′ A (AP f (γ' ₂₁)) b₀₁' b₁₁')
    (q₀₀ : b₀₀' ≡ʰ b₀₀) (q₀₁ : b₀₁' ≡ʰ b₁₀) (q₀₂ : b₀₂' ≡ʰ b₂₀)
    (q₁₀ : b₁₀' ≡ʰ b₀₁) (q₁₁ : b₁₁' ≡ʰ b₁₁) (q₁₂ : b₁₂' ≡ʰ b₂₁)
    (q₂₀ : b₂₀' ≡ʰ b₀₂) (q₂₁ : b₂₁' ≡ʰ b₁₂)
    -- (r₀₂ : a₀₂ ≡ʰ b₀₂) (r₁₂ : a₁₂ ≡ʰ b₁₂) (r₂₀ : a₂₀ ≡ʰ b₂₀) (r₂₁ : a₂₁ ≡ʰ b₂₁)
    (r₂₂ : a₂₂ ≡ʰ b₂₂) →
    sym′ A (AP (AP f) γ) b₀₂ b₁₂ b₂₀ b₂₁ ϕ' b₀₂' b₁₂' b₂₀' b₂₁' q₀₀ q₀₁ q₀₂ q₁₀ q₁₁ q₁₂ q₂₀ q₂₁ b₂₂
    ≡
    {! Id′-AP▸▸ (λ x → A (x ₀)) (λ x → A (pop x ₁)) (λ x → AP f (pop (pop x))) (λ x → top (pop x)) (λ x → top x)
       (γ' ∷ a₀₀' ∷ a₀₁' ∷ a₀₂' ∷ a₁₀' ∷ a₁₁' ∷ a₁₂')
       (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) a₂₀' a₂₁'
       -- sym′ (λ x → A (f x)) γ a₀₂ a₁₂ a₂₀ a₂₁ ϕ a₀₂' a₁₂' a₂₀' a₂₁' e₀₀ e₀₁ e₀₂ e₁₀ e₁₁ e₁₂ e₂₀ e₂₁ a₂₂!}
-}

-- {-# REWRITE sym′-AP #-}

