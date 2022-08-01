{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Types.TelPi where

open import HOTT.Rewrite
open import HOTT.Identity
open import HOTT.Telescope
open import HOTT.Types.Universe

------------------------------------------------------------
-- Identity types of dependent telescope function-types
------------------------------------------------------------

postulate
  ＝ℿ : (Δ : Tel) (T : el Δ → Type) (f g : ℿ Δ T) →
    (f ＝ g) ≡ （ δ ⦂ ID Δ ）⇨ 𝕀𝕕 (𝚲 T) δ (f ⊘ δ ₀) (g ⊘ δ ₁)

{-# REWRITE ＝ℿ #-}

postulate
  AP : {Γ Δ : Tel} (f : el Γ → el Δ) → el (ID Γ) → el (ID Δ)
  ID▸ : (Δ : Tel) (A : Δ ⇨ Type) →
    ID (Δ ▸ A) ≡ᵉ
      (ID Δ ▸ (Λ x ⇨ A ⊘ x ₀) ▸ (Λ x ⇨ A ⊘ pop x ₁) ▸
        (Λ x ⇨ 𝕀𝕕 A (pop (pop x)) (top (pop x)) (top x)))
  AP₀ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → AP f γ ₀ ≡ᵉ f (γ ₀)
  AP₁ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → AP f γ ₁ ≡ᵉ f (γ ₁)

{-# REWRITE ID▸ AP₀ AP₁ #-}

postulate
  ∷₀ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ))
    (a₀ : A (δ ₀)) (a₁ : A (δ ₁)) (a₂ : 𝕀𝕕 (𝚲 A) δ a₀ a₁) →
    (_∷_ {ID Δ} δ a₀ ∷ a₁ ∷ a₂) ₀ ≡ᵉ _∷_ {Δ} {𝚲 A} (δ ₀) a₀
  ∷₁ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ))
    (a₀ : A (δ ₀)) (a₁ : A (δ ₁)) (a₂ : 𝕀𝕕 (𝚲 A) δ a₀ a₁) →
    (_∷_ {ID Δ} δ a₀ ∷ a₁ ∷ a₂) ₁ ≡ᵉ _∷_ {Δ} {𝚲 A} (δ ₁) a₁

{-# REWRITE ∷₀ ∷₁ #-}

postulate
  ap-⊘ⁿᵈ : (Γ Δ : Tel) (T : Type)
    (f : el Γ → （ x ⦂ Δ ）⇨ T) (a : el Γ → el Δ) →
    refl (Λ w ⇨ f w ⊘ a w) ≡ Λ γ ⇨ refl (𝚲 f) ⊘ γ ⊘ (AP a γ)

{-# REWRITE ap-⊘ⁿᵈ #-}

postulate
  ap-⊘ : (Γ Δ : Tel) (T : Δ ⇨ Type)
    (f : el Γ → （ x ⦂ Δ ）⇨ T ⊘ x) (a : el Γ → el Δ) →
    refl (Λ w ⇨ f w ⊘ a w) ≡ Λ γ ⇨ refl (𝚲 f) ⊘ γ ⊘ (AP a γ)

{-# REWRITE ap-⊘ #-}

postulate
  AP-pop : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    AP (λ x → pop (f x)) γ ≡ᵉ pop (pop (pop (AP f γ)))
  pop-pop-pop-AP₀ : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    pop (pop (pop (AP f γ))) ₀ ≡ᵉ pop (f (γ ₀))
  pop-pop-pop-AP₁ : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    pop (pop (pop (AP f γ))) ₁ ≡ᵉ pop (f (γ ₁))

{-# REWRITE AP-pop pop-pop-pop-AP₀ pop-pop-pop-AP₁ #-}

postulate
  top-pop-AP : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (AP f γ)) ≡ top (f (γ ₁))
  top-pop-pop-AP : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (pop (AP f γ))) ≡ top (f (γ ₀))

{-# REWRITE top-pop-AP top-pop-pop-AP #-}

postulate
  ap-top : (Γ Δ : Tel) (A : Δ ⇨ Type) (f : el Γ → el (Δ ▸ A)) →
    refl (Λ x ⇨ top (f x)) ≡ Λ γ ⇨ top (AP f γ)  

{-# REWRITE ap-top #-}
