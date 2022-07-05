{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Sym.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Sym.Base

-- Symmetry relates the two degenerate squares, both for telescopes
-- and for types.

postulate
  AP-REFL′ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) →
    AP (Λ x ⇨ REFL (f x)) γ ≡ᵉ SYM Δ (REFL (AP (Λ x ⇨ f x) γ))

{-# REWRITE AP-REFL′ #-}

Id-AP▸▸ : {Γ Δ : Tel} (B : Δ →Type) (C :  (Δ ▸ B) →Type)
    (f : Γ ⇨ Δ) (g : (x : el Γ) → B ⊘ (f ⊛ x)) (h : (x : el Γ) → C ⊘ (f ⊛ x ∷ g x)) (γ : el (ID Γ))
    (A : (Δ ▸ B ▸ C) →Type) (a₀ : A ⊘ (f ⊛ (γ ₀) ∷ g (γ ₀) ∷ h (γ ₀))) (a₁ : A ⊘ (f ⊛ (γ ₁) ∷ g (γ ₁) ∷ h (γ ₁))) →
    Id A (AP f γ ∷ g (γ ₀) ∷ g (γ ₁) ∷ ap (B ⊚ f) g γ ∷
         h (γ ₀) ∷ h (γ ₁) ∷ {!ap (C ⊚ (Λ x ⇨ f ⊛ x ∷ g x)) h γ!}) a₀ a₁
  ≡ Id (A ⊚ (Λ w ⇨ f ⊛ w ∷ g w ∷ h w)) γ a₀ a₁
Id-AP▸▸ B C f g h γ A a₀ a₁ = {!!}

postulate
  ap-refl : {Δ : Tel} (A : Δ →Type) (f : (x : el Δ) → A ⊘ x) (δ : el (ID Δ)) →
    ap (Λ x ⇒ Id A (REFL x) (f x) (f x)) (λ x → refl (f x)) δ ≡
    {!
    coe→ (Id-AP▸▸ (λ x → A (x ₀)) (λ x → A (pop x ₁)) (λ x → REFL x) (λ x → f x) (λ x → f x) δ
                   (λ y → Id A (pop (pop y)) (top (pop y)) (top y)) (refl (f (δ ₀))) (refl (f (δ ₁))))
    
    (sym A (REFL δ)
       {f (δ ₀)} {f (δ ₀)} (refl (f (δ ₀)))
       {f (δ ₁)} {f (δ ₁)} (refl (f (δ ₁)))
       (ap A f δ) (ap A f δ)
       -- Why doesn't Id-REFL▸▸ fire as a rewrite?
       (coe← (Id-REFL▸▸ (A ⊚ Λ₀) ((A ⊚ Λ₁) ⊚ POP)
                    (Λ y ⇒ Id A (pop (pop y)) (top (pop y)) (top y))
                    δ (f (δ ₀)) (f (δ ₁)) (ap A f δ) (ap A f δ))
             (refl (ap A f δ))))
!}

{-
    coe→ (Id-AP▸▸ (λ x → A (x ₀)) (λ x → A (pop x ₁)) (λ x → REFL x) (λ x → f x) (λ x → f x) δ
                   (λ y → Id A (pop (pop y)) (top (pop y)) (top y)) (refl (f (δ ₀))) (refl (f (δ ₁))))
     (sym A (REFL δ)
       {f (δ ₀)} {f (δ ₀)} (refl (f (δ ₀)))
       {f (δ ₁)} {f (δ ₁)} (refl (f (δ ₁)))
       (ap f δ) (ap f δ) (refl (ap f δ)))

{-# REWRITE ap-refl #-}
-}
