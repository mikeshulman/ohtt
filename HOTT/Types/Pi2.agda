{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Types.Pi2 where

open import HOTT.Rewrite
open import HOTT.Identity
open import HOTT.Telescope
open import HOTT.Types.Pi
open import HOTT.Types.Universe
open import HOTT.Types.TelPi

--------------------------------------------------
-- Identity types of dependent Π-types
--------------------------------------------------

postulate
  ＝Π : (A : Type) (B : A → Type) (f g : Π A B) →
    (f ＝ g) ≡ （ a₀ ⦂ A ）⇒ （ a₁ ⦂ A ）⇒ （ a₂ ⦂ a₀ ＝ a₁ ）⇒ Id (𝛌 B) a₂ (f ∙ a₀) (g ∙ a₁)
{-# REWRITE ＝Π #-}

postulate
  reflΠ : (A : Type) (B : A → Type) → (Π A B ＝U Π A B)
  refl-Π : (A : Type) (B : A → Type) → refl (Π A B) ≡ reflΠ A B
  reflΠ//~ : (A : Type) (B : A → Type) (f g : Π A B) →
    reflΠ A B // f ~ g ≡ (f ＝ g)
  -- TODO: Define the rest of reflΠ (i.e. transport)

{-# REWRITE refl-Π reflΠ//~ #-}

postulate
  apΠ : {Δ : Tel} (A : el Δ → Type) (B : (x : el Δ) → A x → Type) (δ : el (ID Δ)) →
    Π (A (δ ₀)) (B (δ ₀)) ＝U Π (A (δ ₁)) (B (δ ₁))
  ap-Π : {Δ : Tel} (A : el Δ → Type) (B : (x : el Δ) → A x → Type) →
    refl (Λ x ⇨ Π (A x) (B x)) ≡ Λ δ ⇨ apΠ A B δ
  apΠ//~ : {Δ : Tel} (A : el Δ → Type) (B : (x : el Δ) → A x → Type)
    (δ : el (ID Δ)) (f₀ : Π (A (δ ₀)) (B (δ ₀))) (f₁ : Π (A (δ ₁)) (B (δ ₁)))  →
    apΠ A B δ // f₀ ~ f₁ ≡
      （ a₀ ⦂ A (δ ₀)）⇒ （ a₁ ⦂ A (δ ₁)）⇒ （ a₂ ⦂ 𝕀𝕕 (𝚲 A) δ a₀ a₁ ）⇒
        𝕀𝕕 (Λ x ⇨ B (pop {Δ} {𝚲 A} x) (top x)) (δ ∷ a₀ ∷ a₁ ∷ a₂) (f₀ ∙ a₀) (f₁ ∙ a₁)
  -- TODO: Define the rest of apΠ (i.e. transport)

{-# REWRITE ap-Π apΠ//~ #-}

postulate
  refl-ƛ : (A : Type) (B : A → Type) (f : (x : A) → B x) →
    refl (𝛌 f) ≡ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒
    refl {（ x ⦂ (ε ▸ (Λ _ ⇨ A)) ）⇨ B (top x)} (Λ x ⇨ f (top x)) ⊘ ([] ∷ a₀ ∷ a₁ ∷ a₂))
  ap-ƛ : (Δ : Tel) (A : el Δ → Type) (B : (x : el Δ) → A x → Type)
    (f : (x : el Δ) → (y : A x) → B x y) →
    refl (Λ x ⇨ 𝛌 (f x)) ≡ Λ δ ⇨ ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒
    refl (Λ y ⇨ f (pop y) (top y)) ⊘ (δ ∷ a₀ ∷ a₁ ∷ a₂)

{-# REWRITE refl-ƛ ap-ƛ #-}

-- TODO: refl-∙, ap-∙
