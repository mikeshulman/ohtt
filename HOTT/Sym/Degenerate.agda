{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Square.Equality
open import HOTT.Square.Boundary
open import HOTT.Sym.Base

-- TODO: Maybe the version of this for telescopes has to be just admissible.

postulate
  APREFL : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ))
    {α₀₂ β₀₂ : el (ID Δ)} (e₀₂ : α₀₂ ≡ β₀₂)
    {α₁₂ β₁₂ : el (ID Δ)} (e₁₂ : α₁₂ ≡ β₁₂)
    {α₂₀ β₂₀ : el (ID Δ)} (e₂₀ : α₂₀ ≡ β₂₀)
    {α₂₁ β₂₁ : el (ID Δ)} (e₂₁ : α₂₁ ≡ β₂₁) →
    el (SQ Δ)
  AP--REFL : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) →
    AP (λ x → REFL (f x)) γ ≡
    APREFL f γ
      (AP-AP (λ x → REFL (f x)) _₀ γ • rev (SYM₀₂ (REFL (AP f γ))))
      (AP-AP (λ x → REFL (f x)) _₁ γ • rev (SYM₁₂ (REFL (AP f γ))))
      (SYM₂₀ (REFL (AP f γ)))
      (SYM₂₁ (REFL (AP f γ)))
  APREFL-₂₀ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ))
    {α₀₂ β₀₂ : el (ID Δ)} (e₀₂ : α₀₂ ≡ β₀₂)
    {α₁₂ β₁₂ : el (ID Δ)} (e₁₂ : α₁₂ ≡ β₁₂)
    {α₂₀ β₂₀ : el (ID Δ)} (e₂₀ : α₂₀ ≡ β₂₀)
    {α₂₁ β₂₁ : el (ID Δ)} (e₂₁ : α₂₁ ≡ β₂₁) →
    APREFL f γ e₀₂ e₁₂ e₂₀ e₂₁ ₀ ≡ REFL (f (γ ₀))
  APREFL-₂₁ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ))
    {α₀₂ β₀₂ : el (ID Δ)} (e₀₂ : α₀₂ ≡ β₀₂)
    {α₁₂ β₁₂ : el (ID Δ)} (e₁₂ : α₁₂ ≡ β₁₂)
    {α₂₀ β₂₀ : el (ID Δ)} (e₂₀ : α₂₀ ≡ β₂₀)
    {α₂₁ β₂₁ : el (ID Δ)} (e₂₁ : α₂₁ ≡ β₂₁) →
    APREFL f γ e₀₂ e₁₂ e₂₀ e₂₁ ₁ ≡ REFL (f (γ ₁))
  APREFL≡SYM-REFL : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) →
    {α₀₂ β₀₂ : el (ID Δ)} (e₀₂ : α₀₂ ≡ β₀₂)
    {α₁₂ β₁₂ : el (ID Δ)} (e₁₂ : α₁₂ ≡ β₁₂)
    {α₂₀ β₂₀ : el (ID Δ)} (e₂₀ : α₂₀ ≡ β₂₀)
    {α₂₁ β₂₁ : el (ID Δ)} (e₂₁ : α₂₁ ≡ β₂₁) →
    APREFL f γ e₀₂ e₁₂ e₂₀ e₂₁ ≡ SYM Δ (REFL (AP f γ))

{-# REWRITE AP--REFL APREFL-₂₀ APREFL-₂₁ #-}

postulate
  AP-REFL≡SYM-REFL : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) →
    AP (λ x → REFL (f x)) γ ≡ SYM Δ (REFL (AP f γ))
{-
AP-REFL≡SYM-REFL f γ =
  APREFL≡SYM-REFL f γ
    (AP-AP (λ x → REFL (f x)) _₀  γ • rev (SYM₀₂ (REFL (AP f γ))))
    (AP-AP (λ x → REFL (f x)) _₁  γ • rev (SYM₁₂ (REFL (AP f γ))))
    (SYM₂₀ (REFL (AP f γ)))
    (SYM₂₁ (REFL (AP f γ)))
-}

postulate
  APREFL-reflᵉ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ))
    {α₀₂ : el (ID Δ)} {α₁₂ : el (ID Δ)} {α₂₀ : el (ID Δ)} {α₂₁ : el (ID Δ)} →
    APREFL f γ (reflᵉ {a = α₀₂}) (reflᵉ {a = α₁₂}) (reflᵉ {a = α₂₀}) (reflᵉ {a = α₂₁}) ≡ SYM Δ (REFL (AP f γ))

{-
{-# REWRITE APREFL-reflᵉ  #-}

postulate
  APREFL≡SYM-REFL-reflᵉ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ))
    {α₀₂ : el (ID Δ)} {α₁₂ : el (ID Δ)} {α₂₀ : el (ID Δ)} {α₂₁ : el (ID Δ)} →
    APREFL≡SYM-REFL f γ (reflᵉ {a = α₀₂}) (reflᵉ {a = α₁₂}) (reflᵉ {a = α₂₀}) (reflᵉ {a = α₂₁}) ≡ reflᵉ

{-# REWRITE APREFL≡SYM-REFL-reflᵉ #-}
-}

postulate
  ap-refl : {Δ : Tel} (A : el Δ → Type) (f : (x : el Δ) → A x) (δ : el (ID Δ)) →
    ap (λ x → refl (f x)) δ ≡
    {!
    sym A (REFL δ)
      {f (δ ₀)} {f (δ ₀)} (frob₀₂ A (REFL δ) (refl (f (δ ₀))))
      {f (δ ₁)} {f (δ ₁)}
      (frob₁₂ A (REFL δ) (refl (f (δ ₀)))
        -- (coe→ (Id′-AP {ε} {ID Δ ▸ (λ v → A (v ₀))} (λ _ → δ ∷ f (δ ₀)) [] (λ w → A (pop w ₁)) (f (δ ₁)) (f (δ ₁)))
              (refl (f (δ ₁))))
      (ap f δ) (ap f δ)
      {!AP-REFL≡SYM-REFL {Δ} {Δ} (λ x → x) δ!}
      {f (δ ₀)} {f (δ ₁)}
      (frob₀₂ A (SYM Δ (REFL δ)) (ap f δ))
      {f (δ ₀)} {f (δ ₁)}
      (frob₁₂ A (SYM Δ (REFL δ)) (ap f δ) (ap f δ))
      (refl (f (δ ₀)))
      (refl (f (δ ₁)))
      reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ
      (coe→ (Id′-AP {ε} {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A (pop x ₁))} (λ _ → δ ∷ f (δ ₀) ∷ f (δ ₁)) []
                   (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
                   (ap f δ) (ap f δ))
            (refl (ap f δ)))
           !}
