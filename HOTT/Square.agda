{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Square where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

--------------------
-- Squares
--------------------

-- With the "bundled, collated" definition of identity telescopes, the
-- definition of square telescopes is trivial.
SQ : Tel → Tel
SQ Δ = ID (ID Δ)

-- It's also easy to define the pieces of the boundary of such a square.

infix 10 _₀₀ _₀₁ _₀₂ _₁₀ _₁₁ _₁₂ _₂₀ _₂₁

-- Beta-reducing by hand, we get:

-- ID (Δ ▸ A)      = (δ : ID Δ) ▸ (a₀ : A) ▸ (a₁ ▸ A) ▸ (a₂ : Id′ A δ a₀ a₁)
-- ID (ID (Δ ▸ A))
--  = ID ( (δ : ID Δ) ▸ (a₀ : A)
--                    ▸ (a₁ : A)
--                    ▸ (a₂ : Id′ A δ a₀ a₁) )
--  = (δ : ID (ID A)) ▸ (a₀₀ : A) ▸ (a₀₁ : A) ▸ (a₀₂ : Id′ A ? a₀₀ a₀₁)
--                    ▸ (a₁₀ : A) ▸ (a₁₁ : A) ▸ (a₁₂ : Id′ A ? a₀₀ a₀₁)
--                    ▸ (a₂₀ : Id′ A ? a₀₀ a₁₀) ▸ (a₂₁ : Id′ A ? a₀₁ a₁₁) ▸ (a₁₂ : Id′ (Id′ A) ? a₂₀ a₂₁)

-- Now a first _₀ picks out the first component of each triple produced by the *outermost* ID.  Thus we have

_₀₀ : {Δ : Tel} → el (SQ Δ) → el Δ
δ ₀₀ = δ ₀ ₀

_₁₀ : {Δ : Tel} → el (SQ Δ) → el Δ
δ ₁₀ = δ ₀ ₁                    -- Note reversal!

_₂₀ : {Δ : Tel} → el (SQ Δ) → el (ID Δ)
δ ₂₀ = δ ₀

-- Similarly, a first _₁ picks out the second component of each triple.

_₀₁ : {Δ : Tel} → el (SQ Δ) → el Δ
δ ₀₁ = δ ₁ ₀

_₁₁ : {Δ : Tel} → el (SQ Δ) → el Δ
δ ₁₁ = δ ₁ ₁

_₂₁ : {Δ : Tel} → el (SQ Δ) → el (ID Δ)
δ ₂₁ = δ ₁

-- The other two boundaries δ₀₂ and δ₁₂ seem trickier, but they are
-- actually just AP of _₀ and _₁.

_₀₂ : {Δ : Tel} → el (SQ Δ) → el (ID Δ)
δ ₀₂ = AP _₀ δ

_₁₂ : {Δ : Tel} → el (SQ Δ) → el (ID Δ)
δ ₁₂ = AP _₁ δ

-- Our existing rewrite rules give us the cubical identities definitionally.

₀₂-₀ : {Δ : Tel} (δ : el (SQ Δ)) → (δ ₀₂ ₀) ≡ (δ ₀₀)
₀₂-₀ δ = reflᵉ

₀₂-₁ : {Δ : Tel} (δ : el (SQ Δ)) → (δ ₀₂ ₁) ≡ (δ ₀₁)
₀₂-₁ δ = reflᵉ

₁₂-₀ : {Δ : Tel} (δ : el (SQ Δ)) → (δ ₁₂ ₀) ≡ (δ ₁₀)
₁₂-₀ δ = reflᵉ

₁₂-₁ : {Δ : Tel} (δ : el (SQ Δ)) → (δ ₁₂ ₁) ≡ (δ ₁₁)
₁₂-₁ δ = reflᵉ

-- We can now extract a definition of squares in a type by having Agda
-- normalize (SQ (Δ ▸ A)) for us.  On my laptop this takes:

-- > 15 sec if only the definition of ID is known
-- > 30 sec once AP₀ and AP₁ are declared as rewrites
-- > 1 min once REFL₀ and REFL₁ are also declared as rewrites
-- > 1 min 30 sec once Id′-REFL and AP-const are also declared as rewrites

-- Once done and cleaned up, we obtain:
{-
ID (ID Δ)
▸ (λ x → A (x ₀₀))
▸ (λ x → A ((pop x) ₀₁))
▸ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
▸ (λ x → A ((pop (pop (pop x))) ₁₀))
▸ (λ x → A ((pop (pop (pop (pop x)))) ₁₁))
▸ (λ x → Id′ (λ y → A ((pop y) ₁)) (pop (pop x)) (top (pop x)) (top x))
▸ (λ x → Id′ A (pop (pop (pop (pop (pop (pop x))))) ₀) (top (pop (pop (pop (pop (pop x)))))) (top (pop (pop x))))
▸ (λ x → Id′ A (pop (pop (pop (pop (pop (pop (pop x)))))) ₁) (top (pop (pop (pop (pop (pop x)))))) (top (pop (pop x))))}
▸ (λ x → Id′ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) (pop (pop x)) (top (pop x)) (top x))
-}
-- Here the last term is clearly the type of squares in A.  Rewriting
-- this in terms of its explicit dependencies, we have:

Sq : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
     {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
     {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
     (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) → Type
Sq {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id′ {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A ((pop x) ₁))}
      (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ coe← (Id′-AP (_₀ {Δ}) δ A a₀₀ a₀₁) a₀₂ ∷
           a₁₀ ∷ a₁₁ ∷ coe← (Id′-AP≡ (λ x → (pop x) ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ coe← (Id′-AP _₀ δ A a₀₀ a₀₁) a₀₂) (δ ₁₂)
                                      (AP-AP (pop {B = λ x → A (x ₀)}) (_₁ {Δ}) (δ ∷ a₀₀ ∷ a₀₁ ∷ coe← (Id′-AP _₀ δ A a₀₀ a₀₁) a₀₂))
                                      A reflʰ reflʰ)
                             a₁₂)
      a₂₀ a₂₁

-- Finally, we can extend a square in a telescope by a square in a type.
sq∷ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
      {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
      {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
      (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁)
      (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
      el (SQ (Δ ▸ A))
sq∷ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ a₂₂ =
  δ ∷ a₀₀ ∷ a₀₁ ∷ coe← (Id′-AP (_₀ {Δ}) δ A a₀₀ a₀₁) a₀₂ ∷
      a₁₀ ∷ a₁₁ ∷ coe← (Id′-AP≡ (λ x → (pop x) ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ coe← (Id′-AP _₀ δ A a₀₀ a₀₁) a₀₂) (δ ₁₂)
                                 (AP-AP (pop {B = λ x → A (x ₀)}) (_₁ {Δ}) (δ ∷ a₀₀ ∷ a₀₁ ∷ coe← (Id′-AP _₀ δ A a₀₀ a₀₁) a₀₂))
                                 A reflʰ reflʰ)
                        a₁₂ ∷
      a₂₀ ∷ a₂₁ ∷ a₂₂

-- This file takes about 3 minutes to typecheck on my laptop, but it does!
