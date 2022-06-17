{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Square.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

------------------------------
-- Square telescopes
------------------------------

-- With the "bundled, collated" definition of identity telescopes, the
-- definition of square telescopes is trivial.
SQ : Tel → Tel
SQ Δ = ID (ID Δ)

-- It's also easy to define the pieces of the boundary of such a square.

infix 40 _₀₀ _₀₁ _₀₂ _₁₀ _₁₁ _₁₂ _₂₀ _₂₁

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

₀₂-₀ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₀₂ ₀ ≡ δ ₀₀
₀₂-₀ δ = reflᵉ

₀₂-₁ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₀₂ ₁ ≡ δ ₀₁
₀₂-₁ δ = reflᵉ

₁₂-₀ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₁₂ ₀ ≡ δ ₁₀
₁₂-₀ δ = reflᵉ

₁₂-₁ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₁₂ ₁ ≡ δ ₁₁
₁₂-₁ δ = reflᵉ

-- We can now extract a definition of squares in a type by having Agda
-- normalize (SQ (Δ ▸ A)) for us.  Once done and cleaned up, we obtain:
{-
ID (ID Δ)
▸ (λ x → A (x ₀₀)
▸ (λ x → A (pop x ₀₁)
▸ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
▸ (λ x → A (pop (x ₀) ₁))
▸ (λ x → A (pop (pop x ₁) ₁))
▸ (λ x → Id′ (λ y → A (pop y ₁)) (pop (pop x)) (top (pop x)) (top x))
▸ (λ x → Id′ A (pop (pop (x ₀))) (top (pop (x ₀))) (top (x ₀)))
▸ (λ x → Id′ A (pop (pop (pop x ₁))) (top (pop (pop x ₁))) (top (pop x ₁)))
▸ (λ x → Id′ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) (pop (pop x)) (top (pop x)) (top x))
-}
-- Here the last term is clearly the type of squares in A.  Rewriting
-- this in terms of its explicit dependencies, we obtain a definition
-- of squares in a type, with boundary slightly frobnified.

------------------------------
-- Squares in a type
------------------------------

Id′₀₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) (a₀₀ : A (δ ₀₀)) (a₀₁ : A (δ ₀₁)) → Type
Id′₀₂ A δ a₀₀ a₀₁ = Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁

Id′₁₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′₀₂ A δ a₀₀ a₀₁) (a₁₀ : A (δ ₁₀)) (a₁₁ : A (δ ₁₁)) → Type
Id′₁₂ A δ {a₀₀} {a₀₁} a₀₂ a₁₀ a₁₁ = Id′ (λ w → A (pop w ₁)) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) a₁₀ a₁₁

Sq : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
     {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′₀₂ A δ a₀₀ a₀₁)
     {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′₁₂ A δ a₀₂ a₁₀ a₁₁)
     (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) → Type
Sq {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id′ {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A ((pop x) ₁))}
      (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂) a₂₀ a₂₁

popsq : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → el (SQ Δ)
popsq (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = δ

top₀₀ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₀₀)
top₀₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₀₀

top₀₁ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₀₁)
top₀₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₀₁

top₀₂ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id′₀₂ A (popsq δ) (top₀₀ δ) (top₀₁ δ)
top₀₂ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₀₂

top₁₀ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₁₀)
top₁₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₁₀

top₁₁ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₁₁)
top₁₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₁₁

top₁₂ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id′₁₂ A (popsq δ) (top₀₂ δ) (top₁₀ δ) (top₁₁ δ)
top₁₂ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₁₂

top₂₀ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id′ A (popsq δ ₂₀) (top₀₀ δ) (top₁₀ δ)
top₂₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₂₀

top₂₁ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id′ A (popsq δ ₂₁) (top₀₁ δ) (top₁₁ δ)
top₂₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₂₁

top₂₂ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Sq A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
top₂₂ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₂₂

{-
-- The "2-simplex" produced by ulift can be regarded as a square.  (TODO: Where does this go?)
{-
ulift→Sq : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀)
  (a₁ a₁' : A δ₁) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') →
  Sq A (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂) (refl a₀) (utr→ A δ₂ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
-}

-}
