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

-- ID (Δ ▸ A)      = (δ : ID Δ) ▸ (a₀ : A) ▸ (a₁ ▸ A) ▸ (a₂ : Id A δ a₀ a₁)
-- ID (ID (Δ ▸ A))
--  = ID ( (δ : ID Δ) ▸ (a₀ : A)
--                    ▸ (a₁ : A)
--                    ▸ (a₂ : Id A δ a₀ a₁) )
--  = (δ : ID (ID A)) ▸ (a₀₀ : A) ▸ (a₀₁ : A) ▸ (a₀₂ : Id A ? a₀₀ a₀₁)
--                    ▸ (a₁₀ : A) ▸ (a₁₁ : A) ▸ (a₁₂ : Id A ? a₀₀ a₀₁)
--                    ▸ (a₂₀ : Id A ? a₀₀ a₁₀) ▸ (a₂₁ : Id A ? a₀₁ a₁₁) ▸ (a₁₂ : Id (Id A) ? a₂₀ a₂₁)

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

------------------------------
-- Squares in a type
------------------------------

-- We can now extract a definition of squares in a type by having Agda
-- normalize (SQ (Δ ▸ A)) for us.  Once done and cleaned up, we obtain:
{-
ID (ID Δ)
▸ (λ x → A (x ₀₀)
▸ (λ x → A (pop x ₀₁)
▸ (λ x → Id (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
▸ (λ x → A (pop (x ₀) ₁))
▸ (λ x → A (pop (pop x ₁) ₁))
▸ (λ x → Id (λ y → A (pop y ₁)) (pop (pop x)) (top (pop x)) (top x))
▸ (λ x → Id A (pop (pop (x ₀))) (top (pop (x ₀))) (top (x ₀)))
▸ (λ x → Id A (pop (pop (pop x ₁))) (top (pop (pop x ₁))) (top (pop x ₁)))
▸ (λ x → Id (λ y → Id A (pop (pop y)) (top (pop y)) (top y)) (pop (pop x)) (top (pop x)) (top x))
-}
-- Here the last term is clearly the type of squares in A.  Rewriting
-- this in terms of its explicit dependencies, we obtain a definition
-- of squares in a type.

-- However, note that the ₀₂ and ₁₂ boundaries are slightly
-- frobnified, living in an identity type that differs from the
-- obvious one by an Id-AP.  For convenience, we introduce names for
-- these variant identity types.

Id₀₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) (a₀₀ : A (δ ₀₀)) (a₀₁ : A (δ ₀₁)) → Type
Id₀₂ A δ a₀₀ a₀₁ = Id (λ x → A (x ₀)) δ a₀₀ a₀₁

Id₁₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁) (a₁₀ : A (δ ₁₀)) (a₁₁ : A (δ ₁₁)) → Type
Id₁₂ A δ {a₀₀} {a₀₁} a₀₂ a₁₀ a₁₁ = Id (λ w → A (pop w ₁)) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) a₁₀ a₁₁

Sq : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
     {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁)
     {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id₁₂ A δ a₀₂ a₁₀ a₁₁)
     (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) → Type
Sq {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A ((pop x) ₁))}
      (λ y → Id A (pop (pop y)) (top (pop y)) (top y))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂) a₂₀ a₂₁

-- We can extend a square telescope by a square in a type together
-- with its boundary.
sq∷ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
     {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁)
     {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id₁₂ A δ a₀₂ a₁₀ a₁₁)
     (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁)
     (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
     el (SQ (Δ ▸ A))
sq∷ A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ a₂₂ =
  δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂

-- And we can extract the pieces of a square in an extended telescope.
popsq : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → el (SQ Δ)
popsq (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = δ

top₀₀ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₀₀)
top₀₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₀₀

top₀₁ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₀₁)
top₀₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₀₁

top₀₂ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id₀₂ A (popsq δ) (top₀₀ δ) (top₀₁ δ)
top₀₂ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₀₂

top₁₀ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₁₀)
top₁₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₁₀

top₁₁ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₁₁)
top₁₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₁₁

top₁₂ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id₁₂ A (popsq δ) (top₀₂ δ) (top₁₀ δ) (top₁₁ δ)
top₁₂ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₁₂

top₂₀ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id A (popsq δ ₂₀) (top₀₀ δ) (top₁₀ δ)
top₂₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₂₀

top₂₁ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id A (popsq δ ₂₁) (top₀₁ δ) (top₁₁ δ)
top₂₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₂₁

-- This, in particular, is much simpler than it would be without
-- Id-AP as a rewrite!
top₂₂ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Sq A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
top₂₂ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₂₂

--------------------------------------------------
-- Computing boundaries of extended squares
--------------------------------------------------

-- Since _₂₀ and _₂₁ are defined in terms of _₀ and _₁, they compute
-- without a problem.  However, _₀₂ and _₁₂ don't compute as defined,
-- because AP computes only when its bound term has a head of ∷, while
-- _₀ and _₁ are defined by pattern-matching.  Thus, we assert the
-- correct computation rules for _₀₂ and _₁₂ on squares in an extended
-- telescope as postulated rewrites.  (It isn't necessary to do this
-- for the empty telescope, since AP-const applies in that case.)

postulate
  sq∷₀₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id₁₂ A δ a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁)
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
    AP _₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) ≡ δ ₀₂ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂
  sq∷₁₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id₁₂ A δ a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁)
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
    AP _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) ≡
      δ ₁₂ ∷ a₁₀ ∷ a₁₁ ∷ Id-pop← (λ x → A (x ₁)) (λ x → A (x ₀)) δ a₀₂ a₁₂

{-# REWRITE sq∷₀₂ sq∷₁₂ #-}

-- We might hope to define the behavior of (AP (λ x → f x ₀)) more
-- generally for any function f.  The definitions would be something
-- like this:

{-
postulate
  AP-₀ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (ID (Δ ▸ A))) (γ : el (ID Γ)) →
    AP (λ x → f x ₀) γ ≡
    AP (λ x → pop (pop (pop (f x))) ₀) γ
    ∷ top (pop (pop (f (γ ₀))))
    ∷ top (pop (pop (f (γ ₁))))
    ∷ ap (λ x → top (pop (pop (f x)))) γ
  AP-₁ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (ID (Δ ▸ A))) (γ : el (ID Γ)) →
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
