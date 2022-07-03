{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Square.Extended where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base

-- We can extend a square telescope by a square in a type together
-- with its boundary.

module Sq∷ {Δ : Tel} (A : Δ ⇨ Type) (δ : el (SQ Δ))
  {a₀₀ : A ⊘ (δ ₀₀)} {a₀₁ : A ⊘ (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A ⊘ (δ ₁₀)} {a₁₁ : A ⊘ (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁)
  (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁)
  (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) where

  -- abstract
  sq∷ : el (SQ (Δ ▸ A))
  sq∷ = δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂

  sq∷₀₀ : _₀ {Δ ▸ A} (_₀ {ID (Δ ▸ A)} sq∷) ≡ᵉ δ ₀₀ ∷ a₀₀
  sq∷₀₀ = reflᵉᵉ

  sq∷₀₁ : _₀ {Δ ▸ A} (_₁ {ID (Δ ▸ A)} sq∷) ≡ᵉ δ ₀₁ ∷ a₀₁
  sq∷₀₁ = reflᵉᵉ

  sq∷₁₀ : _₁ {Δ ▸ A} (_₀ {ID (Δ ▸ A)} sq∷) ≡ᵉ δ ₁₀ ∷ a₁₀
  sq∷₁₀ = reflᵉᵉ

  sq∷₁₁ : _₁ {Δ ▸ A} (_₁ {ID (Δ ▸ A)} sq∷) ≡ᵉ δ ₁₁ ∷ a₁₁
  sq∷₁₁ = reflᵉᵉ

  sq∷₂₀ : _₀ {ID (Δ ▸ A)} sq∷ ≡ᵉ δ ₂₀ ∷ a₀₀ ∷ a₁₀ ∷ a₂₀
  sq∷₂₀ = reflᵉᵉ

  sq∷₂₁ : _₁ {ID (Δ ▸ A)} sq∷ ≡ᵉ δ ₂₁ ∷ a₀₁ ∷ a₁₁ ∷ a₂₁
  sq∷₂₁ = reflᵉᵉ

-- Since _₂₀ and _₂₁ are defined in terms of _₀ and _₁, they compute
-- without a problem.  However, _₀₂ and _₁₂ don't compute as defined,
-- because AP computes only when its bound term has a head of ∷, while
-- _₀ and _₁ are defined by pattern-matching.  Thus, we assert the
-- correct computation rules for _₀₂ and _₁₂ on squares in an extended
-- telescope as postulated rewrites.  (It isn't necessary to do this
-- for the empty telescope, since AP-const applies in that case.)

  postulate
    sq∷₀₂ : AP (Λ₀ {Δ ▸ A}) sq∷ ≡ᵉ δ ₀₂ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂
    sq∷₁₂ : AP (Λ₁ {Δ ▸ A}) sq∷ ≡ᵉ δ ₁₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂

open Sq∷ public

{-# REWRITE sq∷₀₂ sq∷₁₂ #-}

-- We might hope to define the behavior of (AP (λ x → f x ₀)) more
-- generally for any function f.  The definitions would be something
-- like this:

{-
postulate
  AP-₀ : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : el Γ → el (ID (Δ ▸ A))) (γ : el (ID Γ)) →
    AP (λ x → f x ₀) γ ≡
    AP (λ x → pop (pop (pop (f x))) ₀) γ
    ∷ top (pop (pop (f (γ ₀))))
    ∷ top (pop (pop (f (γ ₁))))
    ∷ ap (λ x → top (pop (pop (f x)))) γ
  AP-₁ : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : el Γ → el (ID (Δ ▸ A))) (γ : el (ID Γ)) →
    AP (λ x → f x ₁) γ ≡
    AP (λ x → pop (pop (pop (f x))) ₀) γ
    ∷ top (pop (pop (f (γ ₀))))
    ∷ top (pop (pop (f (γ ₁))))
    ∷ ap (λ x → top (pop (pop (f x)))) γ

{-# REWRITE AP-₀ AP-₁ #-}
-}

-- Unfortunately, if we try to use these to replace sq∷₀₂ and sq∷₁₂,
-- the result is unfeasibly slow.  I think that iterated pop/tops are
-- just much slower than pattern-matches against ∷.  I don't know
-- whether these more general rules are needed for anything; if they
-- are, we could try to rewrite them by first appling (AP f) and then
-- a postulated version of (AP _₀).
