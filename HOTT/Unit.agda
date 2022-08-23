{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Unit where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe

postulate
  kan-⊤ : kan ⊤ ≡ bury [≊] {⊤} (λ _ → ⊤) (λ _ _ _ →
    ≊[ (λ _ _ → ⊤) , (ƛ x ⇒ x) , (ƛ x ⇒ x) , (ƛ _ ⇒ ★) , (ƛ _ ⇒ ★) ]
    ) ★
{-# REWRITE kan-⊤ #-}
