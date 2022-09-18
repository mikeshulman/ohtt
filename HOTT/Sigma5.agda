module HOTT.Sigma5 where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube
open import HOTT.Universe
open import HOTT.Functoriality

module _ {A B : Type} {C : A → B → Type} {D : A → Type} {E : B → Type} where

  postulate
    refl-⸴⸴⸴⸴⸴ : (a : A) (b : B) (c : C a b) (d : D a) (e : E b) →
      refl {Σ⁵ A B C D E} (a ⸴ b ⸴ c ⸴ d ⸴ e) ≡ (refl a ⸴ refl b ⸴ refl c ⸴ refl d ⸴ refl e)
    refl-!₀ : (u : Σ⁵ A B C D E) → refl (u !₀) ≡ refl u !₀
    refl-!₁ : (u : Σ⁵ A B C D E) → refl (u !₁) ≡ refl u !₁
  {-# REWRITE refl-⸴⸴⸴⸴⸴ refl-!₀ refl-!₁ #-}

frob-refl-!₂ : {A B : Type} (C : A ⇒ B ⇒ Type) {D : A → Type} {E : B → Type}
  (u : Σ⁵ A B (λ x y → C ∙ x ∙ y) D E) → (u !₂ ＝ u !₂)
frob-refl-!₂ C u = refl u !₂

frob-refl-!⁰ : {A B : Type} {C : A → B → Type} (D : A ⇒ Type) {E : B → Type}
  (u : Σ⁵ A B C (D ∙_) E) → (u !⁰ ＝ u !⁰)
frob-refl-!⁰ D u = refl u !⁰

frob-refl-!¹ : {A B : Type} {C : A → B → Type} {D : A → Type} (E : B ⇒ Type)
  (u : Σ⁵ A B C D (E ∙_)) → (u !¹ ＝ u !¹)
frob-refl-!¹ E u = refl u !¹

module _ {A B : Type} {C : A → B → Type} {D : A → Type} {E : B → Type} where

  postulate
    refl-!₂ : (u : Σ⁵ A B C D E) → refl (u !₂) ≡ frob-refl-!₂ (ƛ x ⇒ ƛ y ⇒ C x y) u
    refl-!⁰ : (u : Σ⁵ A B C D E) → refl (u !⁰) ≡ frob-refl-!⁰ (𝛌 D) u
    refl-!¹ : (u : Σ⁵ A B C D E) → refl (u !¹) ≡ frob-refl-!¹ (𝛌 E) u
  {-# REWRITE refl-!₂ refl-!⁰ refl-!¹ #-}

module _ {Δ : Type} {A B : Δ → Type} {C : (δ : Δ) → A δ → B δ → Type} {D : (δ : Δ) → A δ → Type} {E : (δ : Δ) → B δ → Type}
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) where

  postulate
    Id-Σ⁵ : (u₀ : Σ⁵ (A δ₀) (B δ₀) (C δ₀) (D δ₀) (E δ₀)) (u₁ : Σ⁵ (A δ₁) (B δ₁) (C δ₁) (D δ₁) (E δ₁)) →
      (Id (λ δ → Σ⁵ (A δ) (B δ) (C δ) (D δ) (E δ)) δ₂ u₀ u₁) ≡
      Σ⁵ (Id A δ₂ (u₀ !₀) (u₁ !₀)) (Id B δ₂ (u₀ !₁) (u₁ !₁))
         (λ w₀ w₁ → Id (λ x → C (₁st x) (₂nd x) (₃rd' x)) {δ₀ , u₀ !₀ , u₀ !₁} {δ₁ , u₁ !₀ , u₁ !₁}
           (δ₂ , w₀ , →Id-ap {Σ Δ A} fst (𝛌 B) {δ₀ , u₀ !₀} {δ₁ , u₁ !₀} (δ₂ , w₀) w₁)
           (u₀ !₂) (u₁ !₂))
         (λ w₀ → Id (uncurry D) {δ₀ , u₀ !₀} {δ₁ , u₁ !₀} (δ₂ , w₀) (u₀ !⁰) (u₁ !⁰))
         (λ w₁ → Id (uncurry E) {δ₀ , u₀ !₁} {δ₁ , u₁ !₁} (δ₂ , w₁) (u₀ !¹) (u₁ !¹))
  {-# REWRITE Id-Σ⁵ #-}

  postulate
    ap-⸴⸴⸴⸴⸴ : (a : (δ : Δ) → A δ) (b : (δ : Δ) → B δ) (c : (δ : Δ) → C δ (a δ) (b δ))
      (d : (δ : Δ) → D δ (a δ)) (e : (δ : Δ) → E δ (b δ)) →
      ap {Δ} {λ δ → Σ⁵ (A δ) (B δ) (C δ) (D δ) (E δ)} (λ δ → a δ ⸴ b δ ⸴ c δ ⸴ d δ ⸴ e δ) δ₂ ≡
      (ap a δ₂ ⸴ ap b δ₂ ⸴
      ←Id-ap {Δ} {Σ Δ (λ x → A x × B x)} (λ x → (x , a x , b x)) (ƛ x ⇒ C (fst x) (fst (snd x)) (snd (snd x))) δ₂ (ap c δ₂) ⸴
      ←Id-ap {Δ} {Σ Δ A} (λ x → x , a x) (𝛌 (uncurry D)) δ₂ (ap d δ₂) ⸴
      ←Id-ap {Δ} {Σ Δ B} (λ x → x , b x) (𝛌 (uncurry E)) δ₂ (ap e δ₂))
  {-# REWRITE ap-⸴⸴⸴⸴⸴ #-}

  module _ (u : (δ : Δ) → Σ⁵ (A δ) (B δ) (C δ) (D δ) (E δ)) where

    postulate
      ap-!₀ : ap (λ δ → u δ !₀) δ₂ ≡ ap u δ₂ !₀
      ap-!₁ : ap (λ δ → u δ !₁) δ₂ ≡ ap u δ₂ !₁
    {-# REWRITE ap-!₀ ap-!₁ #-}

    postulate
      ap-!₂ : ap (λ δ → u δ !₂) δ₂ ≡
       →Id-ap {Δ} {Σ Δ (λ x → A x × B x)} (λ x → x , u x !₀ , u x !₁)
              (ƛ x ⇒ C (fst x) (fst (snd x)) (snd (snd x))) δ₂ (ap u δ₂ !₂)
      ap-!⁰ : ap (λ δ → u δ !⁰) δ₂ ≡ →Id-ap {Δ} {Σ Δ A} (λ x → x , u x !₀) (𝛌 (uncurry D)) δ₂ (ap u δ₂ !⁰)
      ap-!¹ : ap (λ δ → u δ !¹) δ₂ ≡ →Id-ap {Δ} {Σ Δ B} (λ x → x , u x !₁) (𝛌 (uncurry E)) δ₂ (ap u δ₂ !¹)
    {-# REWRITE ap-!₂ ap-!⁰ ap-!¹ #-}
