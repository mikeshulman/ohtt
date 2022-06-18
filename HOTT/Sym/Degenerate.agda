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

AP--REFL : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) →
  AP (λ x → REFL (f x)) γ ≡ SYM Δ (REFL (AP f γ))

postulate
  ap-refl : {Δ : Tel} (A : el Δ → Type) (f : (x : el Δ) → A x) (δ : el (ID Δ)) →
    ap (λ x → refl (f x)) δ ≡
    coe← (Id′-AP {Δ} {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))} (λ x → REFL x ∷ f x ∷ f x)
                 δ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) (refl (f (δ ₀))) (refl (f (δ ₁))))
         ((sym A (REFL δ)
             {f (δ ₀)} {f (δ ₀)} (frob₀₂ A (REFL δ) (refl (f (δ ₀))))
             {f (δ ₁)} {f (δ ₁)} (frob₁₂ A (REFL δ) (refl (f (δ ₀))) (refl (f (δ ₁))))
             (ap f δ) (ap f δ)
             (AP--REFL {Δ} {Δ} (λ x → x) δ)
             {f (δ ₀)} {f (δ ₁)} (coe→ (Id′-AP REFL δ (λ z → A (z ₀)) (f (δ ₀)) (f (δ ₁))) (ap f δ))
             {f (δ ₀)} {f (δ ₁)} (coe→ (Id′-AP (λ z → REFL z ∷ f z) δ (λ z → A (pop z ₁)) (f (δ ₀)) (f (δ ₁))) (ap f δ))
             (refl (f (δ ₀))) (refl (f (δ ₁)))
             reflʰ reflʰ (coe→≡ʰ (Id′-AP REFL δ (λ z → A (z ₀)) (f (δ ₀)) (f (δ ₁))) (ap f δ))
             reflʰ reflʰ (coe→≡ʰ (Id′-AP (λ z → REFL z ∷ f z) δ (λ z → A (pop z ₁)) (f (δ ₀)) (f (δ ₁))) (ap f δ))
             (revʰ (frob₀₂≡ A (REFL δ) (refl (f (δ ₀)))))
             (revʰ (frob₁₂≡ A (REFL δ) (refl (f (δ ₀))) (refl (f (δ ₁)))))
             (coe→ (Id′-AP≡ {ε} {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A (pop x ₁))} (λ _ → δ ∷ f (δ ₀) ∷ f (δ ₁)) []
                      (sq₁₂≡ A {REFL δ} {REFL δ} reflᵉ reflʰ reflʰ
                         (coe←≡ʰ (Id′-AP _₀ (REFL δ) A (f (δ ₀)) (f (δ ₀))) (refl (f (δ ₀)))) reflʰ reflʰ
                         (coe←≡ʰ (Id′-AP≡ (λ x → pop x ₁)
                                   (REFL δ ∷ f (δ ₀) ∷ f (δ ₀) ∷
                                     coe← (Id′-AP _₀ (REFL δ) A (f (δ ₀)) (f (δ ₀))) (refl (f (δ ₀))))
                                   (AP-AP pop _₁
                                     (REFL δ ∷ f (δ ₀) ∷ f (δ ₀) ∷ coe← (Id′-AP _₀ (REFL δ) A (f (δ ₀)) (f (δ ₀))) (refl (f (δ ₀)))))
                                   A reflʰ reflʰ)
                                 (refl (f (δ ₁)))
                         •ʰ revʰ (coe→≡ʰ (Id′-AP (λ _ → δ ∷ f (δ ₀)) [] (λ z → A (pop z ₁)) (f (δ ₁)) (f (δ ₁)))
                                          (ap (λ _ → f (δ ₁)) []))))
                      (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
                      {ap f δ} {ap f δ} reflʰ {ap f δ} {ap f δ} reflʰ)
                    (refl (ap f δ)))))

{-# REWRITE ap-refl #-}

AP--REFL f γ = {!!}
