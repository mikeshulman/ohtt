{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Square.Fill where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe.Parametric
open import HOTT.Functoriality
open import HOTT.Square.Simple
open import HOTT.Square.Sym


{-
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
-}
