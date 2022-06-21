{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Square.Equality
open import HOTT.Sym.Base

postulate
  AP-REFL′ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) →
    AP (λ x → REFL (f x)) γ ≡ SYM Δ (REFL (AP f γ))

{-# REWRITE AP-REFL′ #-}

postulate
  ap-refl : {Δ : Tel} (A : el Δ → Type) (f : (x : el Δ) → A x) (δ : el (ID Δ)) →
    ap (λ x → refl (f x)) δ ≡
    coe→ (Id′-AP▸▸ (λ x → A (x ₀)) (λ x → A (pop x ₁)) (λ x → REFL x) (λ x → f x) (λ x → f x) δ
                   (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) (refl (f (δ ₀))) (refl (f (δ ₁))))
     (sym A (REFL δ)
       {f (δ ₀)} {f (δ ₀)} (refl (f (δ ₀)))
       {f (δ ₁)} {f (δ ₁)} (refl (f (δ ₁)))
       (ap f δ) (ap f δ) (refl (ap f δ)))

{-# REWRITE ap-refl #-}
