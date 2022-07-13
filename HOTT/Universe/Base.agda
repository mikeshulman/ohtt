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
a ~[ e ] b = fst (e ↓) ∙ a ∙ b

coe⇒ : {A B : Type} → (A ＝ B) → (A ⇒ B)
coe⇒ e = ƛ x ⇒ fst (fst (fst (snd (e ↓)) ∙ x))

~coe⇒ : {A B : Type} (e : A ＝ B) (a : A) → a ~[ e ] (coe⇒ e ∙ a)
~coe⇒ e a = snd (fst (fst (snd (e ↓)) ∙ a))

ucoe⇒ : {A B : Type} (e : A ＝ B) (a : A) (b₀ b₁ : B) (s₀ : a ~[ e ] b₀) (s₁ : a ~[ e ] b₁) → b₀ ＝ b₁
ucoe⇒ e a b₀ b₁ s₀ s₁ = fst ((snd (fst (snd (e ↓)) ∙ a)) ∙ (b₀ , s₀) ∙ (b₁ , s₁))

u~coe⇒ : {A B : Type} (e : A ＝ B) (a : A) (b₀ b₁ : B) (s₀ : a ~[ e ] b₀) (s₁ : a ~[ e ] b₁) →
  Id {ε▸ B} (Λ x ⇨ (a ~[ e ] top x)) ([] ∷ b₀ ∷ b₁ ∷ ucoe⇒ e a b₀ b₁ s₀ s₁) s₀ s₁
u~coe⇒ e a b₀ b₁ s₀ s₁ = snd ((snd (fst (snd (e ↓)) ∙ a)) ∙ (b₀ , s₀) ∙ (b₁ , s₁))

coe⇐ : {A B : Type} → (A ＝ B) → (B ⇒ A)
coe⇐ e = ƛ y ⇒ fst (fst (snd (snd (e ↓)) ∙ y))

~coe⇐ : {A B : Type} (e : A ＝ B) (b : B) → (coe⇐ e ∙ b) ~[ e ] b
~coe⇐ e b = snd (fst (snd (snd (e ↓)) ∙ b))

ucoe⇐ : {A B : Type} (e : A ＝ B) (b : B) (a₀ a₁ : A) (s₀ : a₀ ~[ e ] b) (s₁ : a₁ ~[ e ] b) → a₀ ＝ a₁
ucoe⇐ e b a₀ a₁ s₀ s₁ = fst ((snd (snd (snd (e ↓)) ∙ b)) ∙ (a₀ , s₀) ∙ (a₁ , s₁))

u~coe⇐ : {A B : Type} (e : A ＝ B) (b : B) (a₀ a₁ : A) (s₀ : a₀ ~[ e ] b) (s₁ : a₁ ~[ e ] b) →
  Id {ε▸ A} (Λ y ⇨ (top y ~[ e ] b)) ([] ∷ a₀ ∷ a₁ ∷ ucoe⇐ e b a₀ a₁ s₀ s₁) s₀ s₁
u~coe⇐ e b a₀ a₁ s₀ s₁ = snd ((snd (snd (snd (e ↓)) ∙ b)) ∙ (a₀ , s₀) ∙ (a₁ , s₁))

postulate
  apU : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) →
    (ap (Λ _ ⇨ Type) A δ) ↓ ≡
    ((ƛ a₀ ⇒ ƛ a₁ ⇒ Id (Λ⇨ A) δ a₀ a₁) ,
    ((ƛ a₀ ⇒ (tr→ (Λ⇨ A) δ a₀ , lift→ (Λ⇨ A) δ a₀) ,
              (ƛ x ⇒ ƛ x' ⇒ (utr→ (Λ⇨ A) δ a₀ (fst x) (fst x') (snd x) (snd x') ,
                             ulift→ (Λ⇨ A) δ a₀ (fst x) (fst x') (snd x) (snd x')))) ,
     (ƛ a₁ ⇒ (tr← (Λ⇨ A) δ a₁ , lift← (Λ⇨ A) δ a₁) ,
              (ƛ x ⇒ ƛ x' ⇒ (utr← (Λ⇨ A) δ a₁ (fst x) (fst x') (snd x) (snd x') ,
                             ulift← (Λ⇨ A) δ a₁ (fst x) (fst x') (snd x) (snd x'))))))

{-# REWRITE apU #-}

----------------------------------------
-- Identity types of type variables
----------------------------------------

-- Id-top, below, depends for its well-typedness on top-pop-pop-AP and
-- top-pop-AP applied at a constant family on the universe.  But even
-- top-pop-pop-AP-const doesn't help, because ＝U reduces even
-- further.  So we declare some additional special rewrites.  (This
-- same problem would happen with any other use of top-pop-pop-AP and
-- top-pop-AP at a particular type, but this is the only place so far
-- where we've needed such a thing.)
postulate
  top-pop-pop-AP-const-U : {Γ Δ : Tel} (f : Γ ⇨ᵉ el (Δ ▸ (Λ _ ⇨ Type))) (γ : el (ID Γ)) →
    top (pop (pop (AP f γ))) ≡ top (f ⊘ᵉ (γ ₀))
  top-pop-AP-const-U : {Γ Δ : Tel} (f : Γ ⇨ᵉ el (Δ ▸ (Λ _ ⇨ Type))) (γ : el (ID Γ)) →
    top (pop (AP f γ)) ≡ top (f ⊘ᵉ (γ ₁))

{-# REWRITE top-pop-pop-AP-const-U top-pop-AP-const-U #-}

postulate
  Id-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) (x₁ : top (f (γ ₁))) →
    Id (Λ x ⇨ top (f x)) γ x₀ x₁ ≡
    fst (top (AP (Λ⇨ᵉ f) γ) ↓) ∙ x₀ ∙ x₁

{-# REWRITE Id-top #-}
