{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Square where

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

record ∂ (A : Type) (a₀₀ a₀₁ a₁₀ a₁₁ : A) : Type where
  constructor ┌─_─┐_□_└─_─┘
  infix 70 _₀₂ _₁₂ _₂₀ _₂₁

  field
    _₁₂ : a₁₀ ＝ a₁₁
    _₂₀ : a₀₀ ＝ a₁₀
    _₂₁ : a₀₁ ＝ a₁₁
    _₀₂ : a₀₀ ＝ a₀₁
open ∂

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

------------------------------
-- Dependent squares
------------------------------

record ∂ᵈ {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁) (a₂₂ : Sq A a)
  (b₀₀ : B ∙ a₀₀) (b₀₁ : B ∙ a₀₁) (b₁₀ : B ∙ a₁₀) (b₁₁ : B ∙ a₁₁) : Type where
  constructor ╔═_═╗_□_╚═_═╝
  infix 70 _₁₂ _₂₀ _₂₁ _₀₂
  field
    _₁₂ : Id (B ∙_) (a ₁₂) b₁₀ b₁₁
    _₂₀ : Id (B ∙_) (a ₂₀) b₀₀ b₁₀
    _₂₁ : Id (B ∙_) (a ₂₁) b₀₁ b₁₁
    _₀₂ : Id (B ∙_) (a ₀₂) b₀₀ b₀₁
open ∂ᵈ

Sqᵈ : {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁)
      (a₂₂ : Sq A ┌─    a ₁₂    ─┐
                  a ₂₀   □    a ₂₁
                  └─    a ₀₂    ─┘)
      {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁} (b : ∂ᵈ B a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) → Type
Sqᵈ {A} B {a₀₀} {a₀₁} {a₁₀} {a₁₁} a a₂₂ {b₀₀} {b₀₁} {b₁₀} {b₁₁} b =
  Id {（ a₀ ⦂ A ）× （ a₁ ⦂ A ）× （ a₂ ⦂ a₀ ＝ a₁ ）× B ∙ a₀ × B ∙ a₁}
      (λ u → Id (B ∙_) (₃rd u) (₄th u) (₅th' u))
      {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀}
      {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁}
      (a ₀₂ , a ₁₂ , a₂₂ , b ₀₂ , b ₁₂)
      (b ₂₀)
      (b ₂₁)


-- Dependent boundaries in constant families are ordinary boundaries
←∂ᵈ-const : {A B : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁}
  {a₂₂ : Sq A ┌─    a ₁₂    ─┐
              a ₂₀   □    a ₂₁
              └─    a ₀₂    ─┘}
  {b₀₀ b₀₁ b₁₀ b₁₁ : B} →
  ∂ᵈ (ƛ _ ⇒ B) a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁ → ∂ B b₀₀ b₀₁ b₁₀ b₁₁
←∂ᵈ-const ╔═  b₁₂  ═╗
          b₂₀  □  b₂₁
          ╚═  b₀₂  ═╝ = ┌─  b₁₂  ─┐
                        b₂₀  □  b₂₁
                        └─  b₀₂  ─┘

-- Dependent squares in constant families are ordinary squares
←Sqᵈ-const :  {A : Type} (B : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁)
  (a₂₂ : Sq A ┌─    a ₁₂    ─┐
              a ₂₀   □    a ₂₁
              └─    a ₀₂    ─┘)
  {b₀₀ b₀₁ b₁₀ b₁₁ : B} (b : ∂ᵈ (ƛ _ ⇒ B) a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
  Sqᵈ {A} (ƛ _ ⇒ B) ┌─   a ₁₂   ─┐
                    a ₂₀  □   a ₂₁
                    └─   a ₀₂   ─┘  a₂₂  ╔═   b ₁₂  ═╗
                                         b ₂₀  □  b ₂₁
                                         ╚═   b ₀₂  ═╝ →
  Sq B ┌─   b ₁₂  ─┐
       b ₂₀  □  b ₂₁
       └─   b ₀₂  ─┘
←Sqᵈ-const {A} B {a₀₀} {a₀₁} {a₁₀} {a₁₁} a a₂₂ {b₀₀} {b₀₁} {b₁₀} {b₁₁} b b₂₂ =
  ←Id-ap {（ a₀ ⦂ A ）× （ a₁ ⦂ A ）× （ a₂ ⦂ a₀ ＝ a₁ ）× B × B} {B × B}
         (λ u → snd (snd (snd u))) (ƛ u ⇒ fst u ＝ snd u)
         {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀} {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁}
         (a ₀₂ , a ₁₂ , a₂₂ , b ₀₂ , b ₁₂) (b ₂₀) (b ₂₁) b₂₂

→Sqᵈ-const :  {A : Type} (B : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁)
  (a₂₂ : Sq A ┌─    a ₁₂    ─┐
              a ₂₀   □    a ₂₁
              └─    a ₀₂    ─┘)
  {b₀₀ b₀₁ b₁₀ b₁₁ : B} (b : ∂ᵈ (ƛ _ ⇒ B) a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
  Sq B ┌─   b ₁₂  ─┐
       b ₂₀  □  b ₂₁
       └─   b ₀₂  ─┘ →
  Sqᵈ {A} (ƛ _ ⇒ B) ┌─   a ₁₂   ─┐
                    a ₂₀  □   a ₂₁
                    └─   a ₀₂   ─┘  a₂₂  ╔═   b ₁₂  ═╗
                                         b ₂₀  □  b ₂₁
                                         ╚═   b ₀₂  ═╝
→Sqᵈ-const {A} B {a₀₀} {a₀₁} {a₁₀} {a₁₁} a a₂₂ {b₀₀} {b₀₁} {b₁₀} {b₁₁} b b₂₂ =
  →Id-ap {（ a₀ ⦂ A ）× （ a₁ ⦂ A ）× （ a₂ ⦂ a₀ ＝ a₁ ）× B × B} {B × B}
         (λ u → snd (snd (snd u))) (ƛ u ⇒ fst u ＝ snd u)
         {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀} {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁}
         (a ₀₂ , a ₁₂ , a₂₂ , b ₀₂ , b ₁₂) (b ₂₀) (b ₂₁) b₂₂

-- Dependent boundaries over refl-refl are ordinary boundaries
←∂ᵈ-refl : {A : Type} (B : A ⇒ Type) (a : A) {b₀₀ b₀₁ b₁₀ b₁₁ : B ∙ a} →
  ∂ᵈ B (refl-∂ a) (refl (refl a)) b₀₀ b₀₁ b₁₀ b₁₁ →
  ∂ (B ∙ a) b₀₀ b₀₁ b₁₀ b₁₁
←∂ᵈ-refl B a ╔═  b₁₂  ═╗
             b₂₀  □  b₂₁
             ╚═  b₀₂  ═╝ = ┌─  b₁₂  ─┐
                           b₂₀  □  b₂₁
                           └─  b₀₂  ─┘

-- Dependent squares over refl-refl are ordinary squares.  This holds
-- definitionally even without nudging!
{-
←Sqᵈ-refl : {A : Type} (B : A ⇒ Type) {a : A} {b₀₀ b₀₁ b₁₀ b₁₁ : B ∙ a}
  (b : ∂ᵈ B (refl-∂ a) (refl (refl a)) b₀₀ b₀₁ b₁₀ b₁₁) →
  Sqᵈ B ┌─    refl a   ─┐
        refl a  □  refl a
        └─    refl a   ─┘  (refl (refl a))   ╔═   b ₁₂  ═╗
                                             b ₂₀  □  b ₂₁
                                             ╚═   b ₀₂  ═╝ →
  Sq (B ∙ a) ┌─   b ₁₂  ─┐
             b ₂₀  □  b ₂₁
             └─   b ₀₂  ─┘
←Sqᵈ-refl {A} B {a} {b₀₀} {b₀₁} {b₁₀} {b₁₁} b b₂₂ = b₂₂
-}

------------------------------
-- Dependent symmetry
------------------------------

postulate
  symᵈ : {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sq A ┌─    a ₁₂    ─┐
                a ₂₀   □    a ₂₁
                └─    a ₀₂    ─┘)
    {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁}
    (b : ∂ᵈ B a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
    Sqᵈ B ┌─   a ₁₂   ─┐
          a ₂₀  □   a ₂₁
          └─   a ₀₂   ─┘     a₂₂       ╔═   b ₁₂  ═╗
                                       b ₂₀  □  b ₂₁
                                       ╚═   b ₀₂  ═╝ →
    Sqᵈ B ┌─   a ₂₁   ─┐
          a ₀₂  □   a ₁₂
          └─   a ₂₀   ─┘ (sym A a a₂₂) ╔═   b ₂₁  ═╗
                                       b ₀₂  □  b ₁₂
                                       ╚═   b ₂₀  ═╝

sym-∂ᵈ : {A : Type} {B : A ⇒ Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁}
    {a₂₂ : Sq A ┌─    a ₁₂    ─┐
                a ₂₀   □    a ₂₁
                └─    a ₀₂    ─┘}
    {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁} →
    ∂ᵈ B a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁ → ∂ᵈ B (sym-∂ a) (sym A a a₂₂) b₀₀ b₁₀ b₀₁ b₁₁
sym-∂ᵈ ╔═  b₁₂  ═╗
       b₂₀  □  b₂₁
       ╚═  b₀₂  ═╝ = ╔═  b₂₁  ═╗
                     b₀₂  □  b₁₂
                     ╚═  b₂₀  ═╝

postulate
  sym-symᵈ : {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sq A ┌─    a ₁₂    ─┐
                a ₂₀   □    a ₂₁
                └─    a ₀₂    ─┘)
    {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁}
    (b : ∂ᵈ B a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
    (b₂₂ : Sqᵈ B ┌─   a ₁₂   ─┐
                 a ₂₀  □   a ₂₁
                 └─   a ₀₂   ─┘  a₂₂  ╔═   b ₁₂  ═╗
                                      b ₂₀  □  b ₂₁
                                      ╚═   b ₀₂  ═╝) →
    symᵈ B (sym-∂ a) (sym A a a₂₂) (sym-∂ᵈ b) (symᵈ B a a₂₂ b b₂₂) ≡ b₂₂
{-# REWRITE sym-symᵈ #-}

postulate
  symᵈ-const : {A B : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sq A ┌─    a ₁₂    ─┐
                a ₂₀   □    a ₂₁
                └─    a ₀₂    ─┘)
    {b₀₀ b₀₁ b₁₀ b₁₁ : B} (b : ∂ᵈ (ƛ _ ⇒ B) a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
    (b₂₂ : Sqᵈ {A} (ƛ _ ⇒ B) ┌─   a ₁₂   ─┐
                             a ₂₀  □   a ₂₁
                             └─   a ₀₂   ─┘  a₂₂  ╔═   b ₁₂  ═╗
                                                  b ₂₀  □  b ₂₁
                                                  ╚═   b ₀₂  ═╝) →
    symᵈ (ƛ _ ⇒ B) a a₂₂ b b₂₂ ≡
    →Sqᵈ-const B (sym-∂ a) (sym A a a₂₂) (sym-∂ᵈ b)
      (sym B (←∂ᵈ-const b) (←Sqᵈ-const B a a₂₂ b b₂₂))
{-# REWRITE symᵈ-const #-}

postulate
  symᵈ-refl : {A : Type} (B : A ⇒ Type) (a : A) {b₀₀ b₀₁ b₁₀ b₁₁ : B ∙ a}
    (b : ∂ᵈ B (refl-∂ a) (refl (refl a)) b₀₀ b₀₁ b₁₀ b₁₁) →
    (b₂₂ : Sqᵈ B ┌─    refl a   ─┐
                 refl a  □  refl a
                 └─    refl a   ─┘  (refl (refl a))   ╔═   b ₁₂  ═╗
                                                      b ₂₀  □  b ₂₁
                                                      ╚═   b ₀₂  ═╝) →
    symᵈ B (refl-∂ a) (refl (refl a)) b b₂₂ ≡
    sym (B ∙ a) (←∂ᵈ-refl B a b) b₂₂
{-# REWRITE symᵈ-refl #-}

------------------------------------------------------------
-- TODO: Dependent square-filling
------------------------------------------------------------
