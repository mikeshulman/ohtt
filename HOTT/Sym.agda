{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square
open import HOTT.Square.Top

------------------------------
-- Symmetry
------------------------------

-- Symmetry for telescopes will be defined in terms of symmetry for types.
SYM : (Δ : Tel) → el (SQ Δ) → el (SQ Δ)

-- We also have to define it mutually with proofs that it transposes the boundary.
SYM₀₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₀ ≡ δ ₀₀
SYM₀₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₀ ≡ δ ₁₀
SYM₀₂ : {Δ : Tel} (δ : el (SQ Δ)) → AP _₀ (SYM Δ δ) ≡ δ ₂₀
SYM₁₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₁ ≡ δ ₀₁
SYM₁₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₁ ≡ δ ₁₁
SYM₁₂ : {Δ : Tel} (δ : el (SQ Δ)) → AP _₁ (SYM Δ δ) ≡ δ ₂₁
SYM₂₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ≡ δ ₀₂
SYM₂₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ≡ δ ₁₂

-- Symmetry for types, of course, is a postulated operation.
postulate
  sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
        {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
        {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
        (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
        Sq A δ a₀₂ a₁₂ a₂₀ a₂₁ →
        Sq A (SYM Δ δ)
             (coe← (Id′≡ A (SYM₀₂ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀)
                         (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)) a₂₀)
             (coe← (Id′≡ A (SYM₁₂ δ) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)
                         (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₂₁)
             (coe← (Id′≡ A (SYM₂₀ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀)
                         (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)) a₀₂)
             (coe← (Id′≡ A (SYM₂₁ δ) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)
                         (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₁₂)

-- Now we can define symmetry for telescopes by decomposing a collated
-- SQ, transposing and applying symmetry, and recomposing again.
SYM ε δ = []
SYM (Δ ▸ A) δ =
  sq∷ A (SYM Δ (popsq δ))
  {coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)}
  {coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)}
  (coe← (Id′≡ A (SYM₀₂ (popsq δ))
                (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)) (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
                (top₂₀ δ))
  {coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)}
  {coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)}
  (coe← (Id′≡ A (SYM₁₂ (popsq δ))
                (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)) (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
                (top₂₁ δ))
  (coe← (Id′≡ A (SYM₂₀ (popsq δ))
                (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)) (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)))
                (top₀₂ δ))
  (coe← (Id′≡ A (SYM₂₁ (popsq δ))
                (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)) (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
                (top₁₂ δ))
  {!sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ) (top₂₂ δ)!}

-- It remains to observe that this definition indeed transposes the boundary.

SYM₀₀ {ε} δ = reflᵉ
SYM₀₀ {Δ ▸ A} δ = {!!}

SYM₀₁ {ε} δ = reflᵉ
SYM₀₁ {Δ ▸ A} δ = {!!}

SYM₀₂ {ε} δ = reflᵉ
SYM₀₂ {Δ ▸ A} δ = {!!}

SYM₁₀ {ε} δ = reflᵉ
SYM₁₀ {Δ ▸ A} δ = {!!}

SYM₁₁ {ε} δ = reflᵉ
SYM₁₁ {Δ ▸ A} δ = {!!}

SYM₁₂ {ε} δ = reflᵉ
SYM₁₂ {Δ ▸ A} δ = {!!}

SYM₂₀ {ε} δ = reflᵉ
SYM₂₀ {Δ ▸ A} δ = {!!}

SYM₂₁ {ε} δ = reflᵉ
SYM₂₁ {Δ ▸ A} δ = {!!}

-- {-# REWRITE SYM₀₀ SYM₀₁ SYM₀₂ SYM₁₀ SYM₁₁ SYM₂₀ SYM₁₂ SYM₂₁ #-}

------------------------------
-- Symmetry is an involution
------------------------------

-- Similarly, we postulate that symmetry on types is an involution,
-- and prove from this that it is an involution on telescopes.

{-
SYM-SYM : (Δ : Tel) (δ : el (SQ Δ)) → SYM Δ (SYM Δ δ) ≡ δ

postulate
  sym-sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
        {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
        {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
        (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
        sym A (SYM Δ δ) a₂₀ a₂₁ a₀₂ a₁₂ (sym A δ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂) ≡ a₂₂

SYM-SYM Δ δ = {!!}

-- {-# REWRITE sym-sym SYM-SYM #-}
-}

{-
postulate
  AP-REFL≡SYM-REFL : (Γ Δ : Tel) (f : el Γ → el Δ) (γ : el (ID Γ)) →
    AP (λ x → REFL (f x)) γ ≡ SYM Δ (REFL (AP f γ))

{-# REWRITE AP-REFL≡SYM-REFL #-}
-}

{- Unported
postulate
  ap-refl : {Δ : Tel} {A : el Δ → Type} (f : (x : el Δ) → A x)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ} (λ w → refl (f w)) {δ₀} {δ₁} δ₂ ≡
    {!sym A (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂) (refl (f δ₀)) (refl (f δ₁)) (ap f δ₂) (ap f δ₂)!}
-}
