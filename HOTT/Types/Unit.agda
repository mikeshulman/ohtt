{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Types.Unit where

open import HOTT.Rewrite
open import HOTT.Identity

------------------------------
-- Unit type
------------------------------

record ⊤ : Type where
  constructor ★

open ⊤

postulate
  ＝⊤ : (u v : ⊤) → (u ＝ v) ≡ ⊤

{-# REWRITE ＝⊤ #-}

postulate
  refl★ : refl ★ ≡ ★

{-# REWRITE refl★ #-}
