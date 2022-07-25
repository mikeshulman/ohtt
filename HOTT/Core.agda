{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Core where

open import HOTT.Rewrite using (Type) public
open import HOTT.Telescope public
open import HOTT.Id public
open import HOTT.Refl public
open import HOTT.Uncoerce public

open import HOTT.Square public
open import HOTT.Sym public
open import HOTT.Transport public
open import HOTT.Fill public

open import HOTT.Unit public
open import HOTT.Sigma public
open import HOTT.Pi public
open import HOTT.Copy public

-- The other pieces of HOTT.Universe are very slow to compile and not
-- needed for our current work in algebra.  So, for now, we leave them
-- out of Core.
open import HOTT.Universe.Base public
open import HOTT.Universe.Transport public

open import HOTT.Groupoids public
open import HOTT.Univalence public
open import HOTT.Prop public
open import HOTT.Decidable public

open import HOTT.Sum public
open import HOTT.Nat public
open import HOTT.Int public
open import HOTT.Empty public
open import HOTT.Bool public
