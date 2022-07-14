{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --experimental-lossy-unification --no-import-sorts #-}

module HOTT.Prop where

open import HOTT.Rewrite using (Type; _≡_; _≡ᵉ_; coe→; coe←)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Square.Base
--open import HOTT.Square.EpBoundary
--open import HOTT.Sym.Base
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Sigma.Base
open import HOTT.Universe.Base
open import HOTT.Groupoids
open import HOTT.Univalence

-- The type of all propositions
Prop : Type
Prop = Σ[ P ⦂ Type ] isProp P
{-
＝Prop : (P Q : Prop) → (P ＝ Q) ＝ ((P → Q) × (Q → P))
＝Prop P Q =

-- Prop is a set
isSet-Prop : isSet Prop
isSet-Prop = ƛ P ⇒ ƛ Q ⇒ ƛ f ⇒ ƛ g ⇒ ?
-}
