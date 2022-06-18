{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Sym.Base

-- Note that DEGSQ-TB does not compute any further yet.  We can
-- emphasize this by writing it as (AP (λ x → REFL x) δ), and noting
-- that AP computes based on the head of its bound term and there is
-- no rule yet when that head is REFL.

-- If the telescope is (Δ ▸ A), we can eta-expand it using the
-- definition of REFL.  (We need to add a coercion because we're not
-- doing a pattern-matching lambda so x isn't definitionally a ∷.)
{-
postulate
  Δ : Tel
  A : el Δ → Type
  δ : el (ID (Δ ▸ A))

eg = AP {Δ ▸ A} {ID (Δ ▸ A)}
        (λ x → REFL (pop x) ∷ top x ∷ top x ∷
               coe→ (Id′-AP (pop {Δ} {A}) (REFL x) A (top x) (top x)) (refl (top x)))
        δ
-}
-- Normalizing the above 'eg' then produces
{-
pop (pop (pop (pop (pop (pop (pop (pop (pop (AP REFL δ)))))))))
∷ top (δ ₀)
∷ top (δ ₁)
∷ coe→ (Id′-AP (λ z → pop (pop (pop (REFL z)))) δ (λ z → A (z ₀)) (top (δ ₀)) (top (δ ₁)))
  (coe← (Id′-AP pop δ A (top (pop (pop δ))) (top (pop δ)))
  (top δ))
∷ top (δ ₀)
∷ top (δ ₁)
∷ coe→ (Id′-AP (λ z → pop (pop (pop (REFL z))) ∷ top z) δ (λ z → A (pop z ₁)) (top (δ ₀)) (top (δ ₁)))
  (coe← (Id′-AP pop δ A (top (pop (pop δ))) (top (pop δ)))
  (top δ))
∷ coe→ (Id′-AP pop (REFL (δ ₀)) A (top (δ ₀)) (top (δ ₀)))
  (top (REFL (δ ₀)))
∷ coe→ (Id′-AP pop (REFL (δ ₁)) A (top (δ ₁)) (top (δ ₁)))
  (top (REFL (δ ₁)))
∷ coe→ (Id′-AP (λ z → pop (pop (pop (REFL z))) ∷ top z ∷ top z) δ
               (λ z → Id′ A (pop (pop z)) (top (pop z)) (top z))
               (coe→ (Id′-AP pop (REFL (δ ₀)) A (top (δ ₀)) (top (δ ₀))) (top (REFL (δ ₀))))
               (coe→ (Id′-AP pop (REFL (δ ₁)) A (top (δ ₁)) (top (δ ₁))) (top (REFL (δ ₁)))))
  (ap (λ z → coe→ (Id′-AP pop (REFL z) A (top z) (top z)) (top (REFL z))) δ)
-}
-- This is just a bunch of coercions, and the computation rules for
-- AP-pop and REFL-pop and refl-top, away from
{-
AP (λ x → REFL (pop x)) δ
  ∷ top (δ ₀) ∷ top (δ ₁) ∷ top δ
  ∷ top (δ ₀) ∷ top (δ ₁) ∷ top δ
  ∷ top (REFL (δ ₀)) ∷ top (REFL (δ ₁)) ∷ ap (λ x → refl (top x)) δ
-}
-- If we also decompose δ as a list:
{-
postulate
  Δ : Tel
  A : el Δ → Type
  δ : el (ID Δ)
  a₀ : A (δ ₀)
  a₁ : A (δ ₁)
  a₂ : Id′ A δ a₀ a₁

eg = AP {Δ ▸ A} {ID (Δ ▸ A)}
        (λ x → REFL (pop x) ∷ top x ∷ top x ∷
               coe→ (Id′-AP (pop {Δ} {A}) (REFL x) A (top x) (top x)) (refl (top x)))
        (δ ∷ a₀ ∷ a₁ ∷ a₂)
-}
-- Then we get similarly
{- pop (pop (pop (pop (pop (pop (pop (pop (pop (AP REFL (δ ∷ a₀ ∷ a₁ ∷ a₂))))))))))
∷ a₀
∷ a₁
∷ coe→ (Id′-AP (λ z → pop (pop (pop (REFL z)))) (δ ∷ a₀ ∷ a₁ ∷ a₂) (λ z → A (z ₀)) a₀ a₁)
  (coe← (Id′-AP pop (δ ∷ a₀ ∷ a₁ ∷ a₂) A a₀ a₁)
  a₂)
∷ a₀
∷ a₁
∷ coe→ (Id′-AP (λ z → pop (pop (pop (REFL z))) ∷ top z) (δ ∷ a₀ ∷ a₁ ∷ a₂) (λ z → A (pop z ₁)) a₀ a₁)
  (coe← (Id′-AP pop (δ ∷ a₀ ∷ a₁ ∷ a₂) A a₀ a₁)
  a₂)
∷ coe→ (Id′-AP pop (REFL (δ ₀) ∷ a₀ ∷ a₀ ∷ refl a₀) A a₀ a₀)
  (refl a₀)
∷ coe→ (Id′-AP pop (REFL (δ ₁) ∷ a₁ ∷ a₁ ∷ refl a₁) A a₁ a₁)
  (refl a₁)
∷ coe→ (Id′-AP (λ z → pop (pop (pop (REFL z))) ∷ top z ∷ top z) (δ ∷ a₀ ∷ a₁ ∷ a₂)
               (λ z → Id′ A (pop (pop z)) (top (pop z)) (top z))
               (coe→ (Id′-AP pop (REFL (δ ₀) ∷ a₀ ∷ a₀ ∷ refl a₀) A a₀ a₀) (refl a₀))
               (coe→ (Id′-AP pop (REFL (δ ₁) ∷ a₁ ∷ a₁ ∷ refl a₁) A a₁ a₁) (refl a₁)))
  (ap (λ z → coe→ (Id′-AP pop (REFL z) A (top z) (top z)) (top (REFL z))) (δ ∷ a₀ ∷ a₁ ∷ a₂))
-}
-- Note that if we remove the coercions, the top of both of these will
-- reduce further by ap-top to a coercion of (top (AP REFL δ)).  So
-- our rewrite system should treat (AP REFL δ) as a basic redex to
-- understand.  We intend to compute it to (SYM (REFL δ)), but this
-- could be problematic because the two don't have the same
-- boundaries, at least on abstract telescopes.  So we coerce them
-- along equalities of those boundaries.

AP-REFL₀₀ : (Δ : Tel) (δ : el (ID Δ)) → (AP REFL δ)₀₀ ≡ (SYM Δ (REFL δ))₀₀
AP-REFL₀₀ Δ δ = reflᵉ

AP-REFL₀₁ : (Δ : Tel) (δ : el (ID Δ)) → (AP REFL δ)₀₁ ≡ (SYM Δ (REFL δ))₀₁
AP-REFL₀₁ Δ δ = reflᵉ

AP-REFL₁₀ : (Δ : Tel) (δ : el (ID Δ)) → (AP REFL δ)₁₀ ≡ (SYM Δ (REFL δ))₁₀
AP-REFL₁₀ Δ δ = reflᵉ

AP-REFL₁₁ : (Δ : Tel) (δ : el (ID Δ)) → (AP REFL δ)₁₁ ≡ (SYM Δ (REFL δ))₁₁
AP-REFL₁₁ Δ δ = reflᵉ

AP-REFL₀₂ : (Δ : Tel) (δ : el (ID Δ)) → (AP REFL δ)₀₂ ≡ (SYM Δ (REFL δ))₀₂
AP-REFL₀₂ ε [] = reflᵉ
AP-REFL₀₂ (Δ ▸ A) (δ ∷ a₀ ∷ a₁ ∷ a₂) =
  AP-AP REFL _₀ (δ ∷ a₀ ∷ a₁ ∷ a₂) •
  {!rev (AP-AP REFL _₀ δ) • AP-REFL₀₂ Δ δ!}
-- This proposed filler for the base equality has type
--- (δ ≡ (SYM Δ (REFL δ))₀₂).
-- But how do we break the left-hand side
--- (AP (λ w → REFL w ₀) (δ ∷ a₀ ∷ a₁ ∷ a₂))
-- down into pieces?

{-
postulate
  AP-REFL≡SYM-REFL : {Δ : Tel} (δ : el (ID Δ)) →
    AP REFL δ ≡ {!SYM Δ (REFL δ)!}
-}
