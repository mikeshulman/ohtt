{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Universe.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Sigma
open import HOTT.Pi
open import HOTT.Copy
open import HOTT.Groupoids

----------------------------------------
-- Identity types of the universe
----------------------------------------

postulate
  ＝U : (A B : Type) → (A ＝ B) ≡ Copy (11Corr A B)

{-# REWRITE ＝U #-}

-- We give names to the pieces of an equality
_~[_]_ : {A B : Type} (a : A) (e : A ＝ B) (b : B) → Type
a ~[ e ] b = fst (snd (snd (e ↓))) ∙ a ∙ b

coe⇒ : {A B : Type} → (A ＝ B) → (A ⇒ B)
coe⇒ e = fst (e ↓)

~coe⇒ : {A B : Type} (e : A ＝ B) (a : A) → a ~[ e ] (coe⇒ e ∙ a)
~coe⇒ e a = fst (snd (snd (snd (e ↓)))) ∙ a

ucoe⇒ : {A B : Type} (e : A ＝ B) (a : A) (b₀ b₁ : B) (s₀ : a ~[ e ] b₀) (s₁ : a ~[ e ] b₁) → b₀ ＝ b₁
ucoe⇒ e a b₀ b₁ s₀ s₁ = fst (fst (snd (snd (snd (snd (snd (e ↓)))))) ∙ a ∙ (b₀ , s₀) ∙ (b₁ , s₁))

u~coe⇒ : {A B : Type} (e : A ＝ B) (a : A) (b₀ b₁ : B) (s₀ : a ~[ e ] b₀) (s₁ : a ~[ e ] b₁) →
  Id {ε▸ B} (Λ x ⇨ (a ~[ e ] top x)) ([] ∷ b₀ ∷ b₁ ∷ ucoe⇒ e a b₀ b₁ s₀ s₁) s₀ s₁
u~coe⇒ e a b₀ b₁ s₀ s₁ = snd (fst (snd (snd (snd (snd (snd (e ↓)))))) ∙ a ∙ (b₀ , s₀) ∙ (b₁ , s₁))

coe⇐ : {A B : Type} → (A ＝ B) → (B ⇒ A)
coe⇐ e = fst (snd (e ↓))

~coe⇐ : {A B : Type} (e : A ＝ B) (b : B) → (coe⇐ e ∙ b) ~[ e ] b
~coe⇐ e b = fst (snd (snd (snd (snd (e ↓))))) ∙ b

ucoe⇐ : {A B : Type} (e : A ＝ B) (b : B) (a₀ a₁ : A) (s₀ : a₀ ~[ e ] b) (s₁ : a₁ ~[ e ] b) → a₀ ＝ a₁
ucoe⇐ e b a₀ a₁ s₀ s₁ = fst (snd (snd (snd (snd (snd (snd (e ↓)))))) ∙ b ∙ (a₀ , s₀) ∙ (a₁ , s₁))

u~coe⇐ : {A B : Type} (e : A ＝ B) (b : B) (a₀ a₁ : A) (s₀ : a₀ ~[ e ] b) (s₁ : a₁ ~[ e ] b) →
  Id {ε▸ A} (Λ y ⇨ (top y ~[ e ] b)) ([] ∷ a₀ ∷ a₁ ∷ ucoe⇐ e b a₀ a₁ s₀ s₁) s₀ s₁
u~coe⇐ e b a₀ a₁ s₀ s₁ = snd (snd (snd (snd (snd (snd (snd (e ↓)))))) ∙ b ∙ (a₀ , s₀) ∙ (a₁ , s₁))

postulate
  apU : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) →
    (ap (Λ _ ⇨ Type) A δ) ↓ ≡
    (ƛ a₀ ⇒ tr→ (Λ⇨ A) δ a₀) ,
    (ƛ a₁ ⇒ tr← (Λ⇨ A) δ a₁) ,
    (ƛ a₀ ⇒ ƛ a₁ ⇒ Id (Λ⇨ A) δ a₀ a₁) ,
    (ƛ a₀ ⇒ lift→ (Λ⇨ A) δ a₀) ,
    (ƛ a₁ ⇒ lift← (Λ⇨ A) δ a₁) ,
    (ƛ a₀ ⇒ ƛ x ⇒ ƛ x' ⇒ (utr→ (Λ⇨ A) δ a₀ (fst x) (fst x') (snd x) (snd x') ,
                          ulift→ (Λ⇨ A) δ a₀ (fst x) (fst x') (snd x) (snd x'))) ,
    (ƛ a₁ ⇒ ƛ x ⇒ ƛ x' ⇒ (utr← (Λ⇨ A) δ a₁ (fst x) (fst x') (snd x) (snd x') ,
                          ulift← (Λ⇨ A) δ a₁ (fst x) (fst x') (snd x) (snd x')))

{-# REWRITE apU #-}
