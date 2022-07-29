{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Identity where

open import HOTT.Rewrite

infix 35 _＝_

------------------------------
-- Homogeneous Id and refl
------------------------------

postulate
  _＝_ : {A : Type} → A → A → Type
  refl : {A : Type} (a : A) → (a ＝ a)
