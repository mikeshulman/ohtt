{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Square.Simple where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe

--------------------
-- Squares
--------------------

-- We introduce a two-dimensional mixfix syntax, using box-drawing
-- symbols, for specifying the boundary of a square.  Hopefully the
-- examples below should make clear how to use it.  When working with
-- this syntax, you may find Emacs's "rectangle" commands helpful.
-- Unfortunately, Agda can't be told to *display* this syntax with
-- appropriate newlines and indentation (I believe Coq could), so it
-- only looks nice in the source code.

record ∂ (A : Type) (a₀₀ a₀₁ a₁₀ a₁₁ : A) : Typeᵉ where
  constructor ┌─_─┐_□_└─_─┘
  infix 70 _₀₂ _₁₂ _₂₀ _₂₁

  field
    _₁₂ : a₁₀ ＝ a₁₁
    _₂₀ : a₀₀ ＝ a₁₀
    _₂₁ : a₀₁ ＝ a₁₁
    _₀₂ : a₀₀ ＝ a₀₁
open ∂ public

Sq : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁) → Type
Sq A {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  Id {A × A} (λ u → fst u ＝ snd u) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a ₀₂ , a ₁₂) (a ₂₀) (a ₂₁)

--------------------
-- Symmetry
--------------------

postulate
  sym : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁) →
    Sq A ┌─   a ₁₂    ─┐
         a ₂₀   □   a ₂₁
         └─   a ₀₂    ─┘  →  Sq A ┌─   a ₂₁    ─┐
                                  a ₀₂   □   a ₁₂
                                  └─   a ₂₀    ─┘

sym-∂ : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → ∂ A a₀₀ a₀₁ a₁₀ a₁₁ → ∂ A a₀₀ a₁₀ a₀₁ a₁₁
sym-∂ ┌─  a₁₂  ─┐
      a₂₀  □  a₂₁
      └─  a₀₂  ─┘ = ┌─  a₂₁  ─┐
                    a₀₂  □  a₁₂
                    └─  a₂₀  ─┘

postulate
  sym-sym : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁) →
    (a₂₂ : Sq A ┌─   a ₁₂    ─┐
                a ₂₀   □   a ₂₁
                └─   a ₀₂    ─┘) → sym A (sym-∂ a) (sym A a a₂₂) ≡ a₂₂
{-# REWRITE sym-sym #-}

refl-∂ : {A : Type} (a : A) → ∂ A a a a a
refl-∂ a = ┌─     refl a     ─┐
           refl a   □    refl a
           └─     refl a     ─┘

-- This relies on Id-refl, for well-typedness.  Like Id-refl and
-- ap-refl, it should be admissible in concrete cases like Σ and Π,
-- but probably must fire explicitly when A is a variable type, or
-- when A is a type like the universe or maybe even any type without
-- an η-rule like a (co)inductive one.  I also don't know how to deal
-- with the case when A is variable or η-free but a is an eliminator,
-- since then (refl a) is volatile and could appear in a reduced form,
-- preventing firing of the rewrite.  It would work if sym reduces on
-- its term argument instead of its type; maybe we could deal with the
-- Π-case of that by *also* inspecting the type when we see that the
-- term is a ƛ?
postulate
  sym-refl-refl : (A : Type) (a : A) → sym A (refl-∂ a) (refl (refl a)) ≡ refl (refl a)
{-# REWRITE sym-refl-refl #-}
-- TODO: Can we replace Id-refl, with a general Id-＝ that uses
-- "heterogeneous" squares associated to squares in the universe?  I
-- think we'll need to say something about Id-＝U, maybe with its own
-- record type.

postulate
  ap-refl-sym : {Δ : Type} (A : Type) (f : Δ → A) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap {Δ} {λ x → f x ＝ f x} (λ x → refl (f x)) δ₂ ≡
    →Id-ap (λ x → (f x , f x)) (ƛ u ⇒ fst u ＝ snd u) {δ₀} {δ₁} δ₂ {refl (f δ₀)} {refl (f δ₁)}
      (sym A ┌─  refl (f δ₁)  ─┐
             ap f δ₂  □  ap f δ₂
             └─  refl (f δ₀)  ─┘  (refl (ap f δ₂)))
{-# REWRITE ap-refl-sym #-}

------------------------------
-- Composition and filling
------------------------------

-- We don't wrap composition and square-filling into ⇒ types, so we
-- name them with → and ← instead of ⇒ and ⇐.

comp→ : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) → a₀₁ ＝ a₁₁
comp→ A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  tr⇒ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₀

fill→ : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) →
  Sq A ┌─  a₁₂  ─┐
       a₂₀  □  comp→ A a₀₂ a₁₂ a₂₀
       └─  a₀₂  ─┘
fill→ A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  lift⇒ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₀

comp← : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₁ : a₀₁ ＝ a₁₁) → a₀₀ ＝ a₁₀
comp← A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  tr⇐ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₁

fill← : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A         ┌─          a₁₂   ─┐
       comp← A a₀₂ a₁₂ a₂₁  □   a₂₁
               └─          a₀₂   ─┘
fill← A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  lift⇐ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₁

comp↑ : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) → a₁₀ ＝ a₁₁
comp↑ A a₀₂ a₂₀ a₂₁ = comp→ A a₂₀ a₂₁ a₀₂

fill↑ : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A ┌─  comp↑ A a₀₂ a₂₀ a₂₁  ─┐
       a₂₀          □          a₂₁
       └─          a₀₂          ─┘
fill↑ A a₀₂ a₂₀ a₂₁ = sym A ┌─  a₂₁                     ─┐
                            a₀₂  □    comp→ A a₂₀ a₂₁ a₀₂
                            └─  a₂₀                     ─┘   (fill→ A a₂₀ a₂₁ a₀₂)

comp↓ : (A : Type) {a₀₀ a₀₁ : A} {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) → a₀₀ ＝ a₀₁
comp↓ A a₁₂ a₂₀ a₂₁ = comp← A a₂₀ a₂₁ a₁₂

fill↓ : (A : Type) {a₀₀ a₀₁ : A} {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A ┌─          a₁₂          ─┐
       a₂₀          □          a₂₁
       └─  comp↓ A a₁₂ a₂₀ a₂₁  ─┘
fill↓ A a₁₂ a₂₀ a₂₁ = sym A ┌─                  a₂₁  ─┐
                            comp← A a₂₀ a₂₁ a₁₂  □  a₁₂
                            └─                  a₂₀  ─┘   (fill← A a₂₀ a₂₁ a₁₂)

--------------------------------------------------
-- 2D syntax for composition and filling
--------------------------------------------------

-- We also introduce a two-dimensional syntax for composition and
-- filling operations, with a double question-mark on the missing side
-- and a triple-arrow denoting the direction of composition or
-- filling.  In order to allow spaces between the double question-mark
-- and the other parts of the notation, we make it a constuctor of a
-- dummy type rather than an actual part of the notation.

record ┬ : Type where
  constructor ⁇

comp_┌─_─┐_⇛_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (_ : ┬) (a₀₂ : a₀₀ ＝ a₀₁) → a₀₁ ＝ a₁₁
comp A ┌─  a₁₂  ─┐
       a₂₀  ⇛    ⁇
       └─  a₀₂  ─┘ = comp→ A a₀₂ a₁₂ a₂₀

-- Note that in the type of the filling operations we still use the
-- linear syntax for compositions; otherwise it would be unreadable.
-- Both syntaxes are useful to have.
fill_┌─_─┐_⇛_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (_ : ┬) (a₀₂ : a₀₀ ＝ a₀₁) →
  Sq A ┌─  a₁₂         ─┐
       a₂₀  □  comp→ A a₀₂ a₁₂ a₂₀
       └─  a₀₂         ─┘
fill A ┌─  a₁₂  ─┐
       a₂₀  ⇛    ⁇
       └─  a₀₂  ─┘ = fill→ A a₀₂ a₁₂ a₂₀

comp_┌─_─┐_⇚_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (_ : ┬) (a₂₁ : a₀₁ ＝ a₁₁) (a₀₂ : a₀₀ ＝ a₀₁) → a₀₀ ＝ a₁₀
comp A ┌─  a₁₂  ─┐
       ⁇    ⇚  a₂₁
       └─  a₀₂  ─┘ = comp← A a₀₂ a₁₂ a₂₁

fill_┌─_─┐_⇚_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (_ : ┬) (a₂₁ : a₀₁ ＝ a₁₁) (a₀₂ : a₀₀ ＝ a₀₁) →
  Sq A ┌─                  a₁₂   ─┐
       comp← A a₀₂ a₁₂ a₂₁  □   a₂₁
       └─                  a₀₂   ─┘
fill A ┌─  a₁₂  ─┐
       ⁇    ⇚  a₂₁
       └─  a₀₂  ─┘ = fill← A a₀₂ a₁₂ a₂₁

comp_┌─_─┐_⤊_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (_ : ┬) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) (a₀₂ : a₀₀ ＝ a₀₁) → a₁₀ ＝ a₁₁
comp A ┌─   ⁇   ─┐
       a₂₀  ⤊  a₂₁
       └─  a₀₂  ─┘ = comp↑ A a₀₂ a₂₀ a₂₁

fill_┌─_─┐_⤊_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (_ : ┬) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) (a₀₂ : a₀₀ ＝ a₀₁) →
  Sq A ┌─  comp↑ A a₀₂ a₂₀ a₂₁  ─┐
       a₂₀          □          a₂₁
       └─          a₀₂          ─┘
fill A ┌─   ⁇   ─┐
       a₂₀  ⤊  a₂₁
       └─  a₀₂  ─┘ = fill↑ A a₀₂ a₂₀ a₂₁

comp_┌─_─┐_⤋_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) (_ : ┬) → a₀₀ ＝ a₀₁
comp A ┌─  a₁₂  ─┐
       a₂₀  ⤋  a₂₁
       └─   ⁇   ─┘ = comp↓ A a₁₂ a₂₀ a₂₁

fill_┌─_─┐_⤋_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) (_ : ┬) →
  Sq A ┌─          a₁₂          ─┐
       a₂₀          □          a₂₁
       └─  comp↓ A a₁₂ a₂₀ a₂₁  ─┘
fill A ┌─  a₁₂  ─┐
       a₂₀  ⤋  a₂₁
       └─   ⁇   ─┘ = fill↓ A a₁₂ a₂₀ a₂₁
