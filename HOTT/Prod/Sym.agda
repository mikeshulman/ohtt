{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Prod.Sym where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Sym.Base
open import HOTT.Prod.Base

postulate
  sym× : {Δ : Tel} (A B : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀) × B (δ ₀₀)} {a₀₁ : A (δ ₀₁) × B (δ ₀₁)}
    (a₀₂ : Id′₀₂ (λ x → A x × B x) δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀) × B (δ ₁₀)} {a₁₁ : A (δ ₁₁) × B (δ ₁₁)}
    (a₁₂ : Id′₁₂ (λ x → A x × B x) δ {a₀₀} {a₀₁} a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id′ (λ x → A x × B x) (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ (λ x → A x × B x) (δ ₂₁) a₀₁ a₁₁)
    (a₂₂ : Sq (λ x → A x × B x) δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁) →
    sym (λ x → A x × B x) δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ a₂₂ ≡
    -- This just needs a Sq-AP lemma
    {!(sym A δ {fst a₀₀} {fst a₀₁} (fst a₀₂) {fst a₁₀} {fst a₁₁}
         (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {fst a₀₀} {fst a₀₁} (fst a₀₂) {fst a₁₀} {fst a₁₁}
           (Id′-pop← (λ x → A (x ₁)) (λ x → A (x ₀) × B (x ₀)) δ {a₀₀} {a₀₁} a₀₂ {fst a₁₀} {fst a₁₁} (fst a₁₂)))
         (fst a₂₀) (fst a₂₁)
         {!fst a₂₂!})!}

{-
postulate
  sym′× : {Δ : Tel} (A B : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀) × B (δ ₀₀)} {a₀₁ : A (δ ₀₁) × B (δ ₀₁)}
    (a₀₂ : Id′₀₂ (λ x → A x × B x) δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀) × B (δ ₁₀)} {a₁₁ : A (δ ₁₁) × B (δ ₁₁)}
    (a₁₂ : Id′₁₂ (λ x → A x × B x) δ {a₀₀} {a₀₁} a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id′ (λ x → A x × B x) (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ (λ x → A x × B x) (δ ₂₁) a₀₁ a₁₁)
    {δ' : el (SQ Δ)} (ϕ : δ' ≡ SYM Δ δ)
    (a₂₂ : Sq (λ x → A x × B x) δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁) →
    sym′ (λ x → A x × B x) δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ ϕ a₂₂ ≡
    (coe← {!Id′-AP (λ x → pop (pop x) ∷ fst (top (pop x)) ∷ fst (top x))
                   (δ' ∷ coe← (cong (λ x → A (x ₀₀) × B (x ₀₀)) ϕ) a₀₀ ∷
       coe← (cong (λ x → A (x ₀₁) × B (x ₀₁)) ϕ) a₁₀
       ∷ sym₀₂ (λ x → A x × B x) δ ϕ a₂₀
       ∷ coe← (cong (λ x → A (x ₁₀) × B (x ₁₀)) ϕ) a₀₁
       ∷ coe← (cong (λ x → A (x ₁₁) × B (x ₁₁)) ϕ) a₁₁
       ∷ sym₁₂ (λ x → A x × B x) δ ϕ a₂₀ a₂₁)
       (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (fst
       (coe←
        (Id′≡ (λ x → A (x ₀) × B (x ₀)) (cong (SYM Δ) ϕ)
         (coe←≡ʰ (cong (λ x → A (x ₀₀) × B (x ₀₀)) ϕ) a₀₀)
         (coe←≡ʰ (cong (λ x → A (x ₁₀) × B (x ₁₀)) ϕ) a₀₁))
        a₀₂))
      !}
       (sym′ A δ {fst a₀₀} {fst a₀₁} (fst a₀₂) {fst a₁₀} {fst a₁₁}
         (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {fst a₀₀} {fst a₀₁} (fst a₀₂) {fst a₁₀} {fst a₁₁}
           (Id′-pop← (λ x → A (x ₁)) (λ x → A (x ₀) × B (x ₀)) δ {a₀₀} {a₀₁} a₀₂ {fst a₁₀} {fst a₁₁} (fst a₁₂)))
         (fst a₂₀) (fst a₂₁) ϕ
         {!fst a₂₂!}) ,
     coe← {!!}
       (sym′ B δ {snd a₀₀} {snd a₀₁} (snd a₀₂) {snd a₁₀} {snd a₁₁}
         (Id′-pop→ (λ x → B (x ₁)) (λ x → B (x ₀)) δ {snd a₀₀} {snd a₀₁} (snd a₀₂) {snd a₁₀} {snd a₁₁}
           (Id′-pop← (λ x → B (x ₁)) (λ x → A (x ₀) × B (x ₀)) δ {a₀₀} {a₀₁} a₀₂ {snd a₁₀} {snd a₁₁} (snd a₁₂)))
         (snd a₂₀) (snd a₂₁) ϕ
         {!snd a₂₂!}))
-}
