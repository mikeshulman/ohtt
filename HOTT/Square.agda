{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Square where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe

----------------------------------------
-- Squares and symmetry
----------------------------------------

Sq : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
  (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) → Type
Sq A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id {A × A} (λ u → fst u ＝ snd u) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) a₂₀ a₂₁

postulate
  sym : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
    (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
    Sq A a₀₂ a₁₂ a₂₀ a₂₁ → Sq A a₂₀ a₂₁ a₀₂ a₁₂

------------------------------
-- Composition and filling
------------------------------

-- We don't wrap composition and square-filling into ⇒ types, so we
-- name them with → and ← instead of ⇒ and ⇐.

comp→ : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) →
  a₀₁ ＝ a₁₁
comp→ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  tr⇒ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₀

fill→ : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) →
  Sq A a₀₂ a₁₂ a₂₀ (comp→ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀)
fill→ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  lift⇒ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₀

comp← : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₁ : a₀₁ ＝ a₁₁) →
  a₀₀ ＝ a₁₀
comp← {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  tr⇐ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₁

fill← : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A a₀₂ a₁₂ (comp← {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁) a₂₁
fill← {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  lift⇐ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₁

comp↑ : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  a₁₀ ＝ a₁₁
comp↑ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ = comp→ {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₀₂

fill↑ : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A a₀₂ (comp↑ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁) a₂₀ a₂₁
fill↑ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
  sym A {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₀₂ (comp→ {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₀₂)
    (fill→ {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₀₂) 

comp↓ : {A : Type} {a₀₀ a₀₁ : A} {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  a₀₀ ＝ a₀₁
comp↓ {A} {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ = comp← {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₁₂

fill↓ : {A : Type} {a₀₀ a₀₁ : A} {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A (comp↓ {A} {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁) a₁₂ a₂₀ a₂₁
fill↓ {A} {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  sym A {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ (comp← {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₁₂) a₁₂
    (fill← {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₁₂)

------------------------------------------------------------
-- TODO: dependent symmetry, dependent square-filling
------------------------------------------------------------
