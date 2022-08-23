{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

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

infix 60 _₀₀ _₀₁ _₀₂ _₁₀ _₁₁ _₁₂ _₂₀ _₂₁

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
δ ₀₂ = AP Λ₀ δ

_₁₂ : {Δ : Tel} → el (SQ Δ) → el (ID Δ)
δ ₁₂ = AP Λ₁ δ

-- Our existing rewrite rules give us the cubical identities definitionally.

₀₂-₀ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₀₂ ₀ ≡ᵉ δ ₀₀
₀₂-₀ δ = reflᵉᵉ

₀₂-₁ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₀₂ ₁ ≡ᵉ δ ₀₁
₀₂-₁ δ = reflᵉᵉ

₁₂-₀ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₁₂ ₀ ≡ᵉ δ ₁₀
₁₂-₀ δ = reflᵉᵉ

₁₂-₁ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₁₂ ₁ ≡ᵉ δ ₁₁
₁₂-₁ δ = reflᵉᵉ

------------------------------
-- Squares in a type
------------------------------

-- We can now extract a definition of squares in a type by having Agda
-- normalize (SQ (Δ ▸ A)) for us.
{-
eg : (Δ : Tel) (A : Δ ⇨ Type) → Type
eg Δ A = {! SQ (Δ ▸ A) !}
-}
-- Once done and cleaned up, we obtain:
{-
ID (ID Δ)
▸ A ⊚ Λ₀ ⊚ᵉ Λ₀
▸ A ⊚ Λ₀ ⊚ᵉ Λ₁ ⊚ᵉ POP
▸ (Λ x ⇨ Id A (AP Λ₀ (pop (pop x))) (top (pop x)) (top x))
▸ A ⊚ Λ₁ ⊚ᵉ POP ⊚ᵉ Λ₀
▸ A ⊚ Λ₁ ⊚ᵉ POP ⊚ᵉ Λ₁ ⊚ᵉ POP
▸ (Λ x ⇨ Id A (AP Λ₁ (pop (pop (pop (pop (pop x)))))) (top (pop x)) (top x))
▸ (Λ x ⇨ Id A (pop (pop x)) (top (pop x)) (top x)) ⊚ Λ₀
▸ (Λ x ⇨ Id A (pop (pop x)) (top (pop x)) (top x)) ⊚ Λ₁ ⊚ᵉ POP
▸ (Λ x ⇨ Id (Λ y ⇨ Id A (pop (pop y)) (top (pop y)) (top y))) (pop (pop x)) (top (pop x)) (top x))
-}
-- The first, second, fourth, and fifth terms are the corners of the
-- square in A, while the third, sixth, seventh, and eighth are its
-- edges.  Note that the edges are all identifications in, literally,
-- A.  This is due to our postulated ⊚ and our rewrite Id-AP⊚;
-- otherwise at least two of them would be identifications in (λ x → A
-- (x ₀)) and (λ x → A (pop x ₁)), which are only related to
-- identifications in A by a coercions along Id-AP.

-- The final term above is clearly the type of squares in A.
-- Rewriting this in terms of its explicit dependencies, we obtain a
-- definition of squares in a type.

Sq : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (SQ Δ))
     {a₀₀ : A ⊘ (δ ₀₀)} {a₀₁ : A ⊘ (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
     {a₁₀ : A ⊘ (δ ₁₀)} {a₁₁ : A ⊘ (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁)
     (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) → Type
Sq {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id {ID▸▸ A} (Id/ A) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂) a₂₀ a₂₁

-- We can extract the pieces of a square in an extended telescope.
popsq : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) → el (SQ Δ)
popsq (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = δ

top₀₀ : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) → A ⊘ (popsq {Δ} {A} δ ₀₀)
top₀₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₀₀

top₀₁ : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) → A ⊘ (popsq {Δ} {A} δ ₀₁)
top₀₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₀₁

top₀₂ : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) →
  Id A (popsq {Δ} {A} δ ₀₂) (top₀₀ {Δ} {A} δ) (top₀₁ {Δ} {A} δ)
top₀₂ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₀₂

top₁₀ : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) → A ⊘ (popsq {Δ} {A} δ ₁₀)
top₁₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₁₀

top₁₁ : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) → A ⊘ (popsq {Δ} {A} δ ₁₁)
top₁₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₁₁

top₁₂ : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) →
  Id A (popsq {Δ} {A} δ ₁₂) (top₁₀ {Δ} {A} δ) (top₁₁ {Δ} {A} δ)
top₁₂ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₁₂

top₂₀ : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) →
  Id A (popsq {Δ} {A} δ ₂₀) (top₀₀ {Δ} {A} δ) (top₁₀ {Δ} {A} δ)
top₂₀ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₂₀

top₂₁ : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) →
  Id A (popsq {Δ} {A} δ ₂₁) (top₀₁ {Δ} {A} δ) (top₁₁ {Δ} {A} δ)
top₂₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₂₁

-- This, in particular, is much simpler than it would be without
-- Id-AP as a rewrite!
top₂₂ : {Δ : Tel} {A : Δ ⇨ Type} (δ : el (SQ (Δ ▸ A))) →
  Sq A (popsq {Δ} {A} δ) {top₀₀ {Δ} {A} δ} {top₀₁ {Δ} {A} δ} (top₀₂ {Δ} {A} δ)
       {top₁₀ {Δ} {A} δ} {top₁₁ {Δ} {A} δ} (top₁₂ {Δ} {A} δ) (top₂₀ {Δ} {A} δ) (top₂₁ {Δ} {A} δ)
top₂₂ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) = a₂₂

-- We can extend a square telescope by a square in a type together
-- with its boundary.
module Sq∷ {Δ : Tel} (A : Δ ⇨ Type) (δ : el (SQ Δ))
  {a₀₀ : A ⊘ (δ ₀₀)} {a₀₁ : A ⊘ (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A ⊘ (δ ₁₀)} {a₁₁ : A ⊘ (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁)
  (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁)
  (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) where

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
