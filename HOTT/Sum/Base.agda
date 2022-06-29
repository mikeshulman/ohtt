{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Sum.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Unit
open import HOTT.Sigma.Base

data sum (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) : Ω → Type where
  inl : (a : A) → sum Ω α β (α a)
  inr : (b : B) → sum Ω α β (β b)

sum≡ : {Ω₀ Ω₁ : Type} (Ω₂ : Ω₀ ≡ Ω₁)
  {A₀ A₁ : Type} (A₂ : A₀ ≡ A₁) {B₀ B₁ : Type} (B₂ : B₀ ≡ B₁)
  {α₀ : A₀ → Ω₀} {α₁ : A₁ → Ω₁} (α₂ : α₀ ≡ʰ α₁)
  {β₀ : B₀ → Ω₀} {β₁ : B₁ → Ω₁} (β₂ : β₀ ≡ʰ β₁)
  {ω₀ : Ω₀} {ω₁ : Ω₁} (ω₂ : ω₀ ≡ʰ ω₁) →
  sum Ω₀ α₀ β₀ ω₀ ≡ sum Ω₁ α₁ β₁ ω₁
sum≡ reflᵉ reflᵉ reflᵉ reflʰ reflʰ reflʰ = reflᵉ

case : {Ω : Type} {A B : Type} {α : A → Ω} {β : B → Ω}
  (ω : Ω) (s : sum Ω α β ω)
  (C : (x : Ω) → sum Ω α β x → Type)
  (f : (a : A) → C (α a) (inl a)) (g : (b : B) → C (β b) (inr b))
  → C ω s
case _ (inl a) C f g = f a
case _ (inr b) C f g = g b

_⊎_ : Type → Type → Type
A ⊎ B = sum ⊤ {A} {B} (λ _ → ★) (λ _ → ★) ★

＝Ω : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) → Type
＝Ω Ω α β = Σ[ x₀ ﹕ Ω ] Σ[ x₁ ﹕ Ω ] Σ[ x₂ ﹕ x₀ ＝ x₁ ] Σ[ s₀ ﹕ sum Ω α β x₀ ] sum Ω α β x₁

＝IDty : (A : Type) → Type
＝IDty A = Σ[ a₀ ﹕ A ] Σ[ a₁ ﹕ A ] (a₀ ＝ a₁)

＝α : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) → ＝IDty A → ＝Ω Ω α β
＝α Ω α β z = (α (π₁ z) ﹐ α (π₁ (π₂ z)) ﹐
                  ap (λ x → α (top x)) ([] ∷ π₁ z ∷ π₁ (π₂ z) ∷ π₂ (π₂ z)) ﹐
                  inl (π₁ z) ﹐ inl (π₁ (π₂ z)))

＝β : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) → ＝IDty B → ＝Ω Ω α β
＝β Ω α β z = (β (π₁ z) ﹐ β (π₁ (π₂ z)) ﹐
                  ap (λ x → β (top x)) ([] ∷ π₁ z ∷ π₁ (π₂ z) ∷ π₂ (π₂ z)) ﹐
                  inr (π₁ z) ﹐ inr (π₁ (π₂ z)))

Id-Ω : {Δ : Tel} (Ω : el Δ → Type) {A B : el Δ → Type}
  (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x) →
  (δ : el (ID Δ)) → Type
Id-Ω {Δ} Ω {A} {B} α β δ =
  Σ[ x₀ ﹕ Ω (δ ₀) ] Σ[ x₁ ﹕ Ω (δ ₁) ] Σ[ x₂ ﹕ Id Ω δ x₀ x₁ ]
  Σ[ s₀ ﹕ sum (Ω (δ ₀)) (λ z → α (δ ₀) z) (λ z → β (δ ₀) z) x₀ ]
           sum (Ω (δ ₁)) (λ z → α (δ ₁) z) (λ z → β (δ ₁) z) x₁

Id-IDty : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) → Type
Id-IDty {Δ} A δ = Σ[ a₀ ﹕ A (δ ₀) ] Σ[ a₁ ﹕ A (δ ₁) ] Id A δ a₀ a₁

Id-α : {Δ : Tel} (Ω : el Δ → Type) {A B : el Δ → Type}
  (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
  (δ : el (ID Δ)) (a : Id-IDty A δ) → Id-Ω Ω {A} {B} α β δ
Id-α {Δ} Ω {A} {B} α β δ a =
  (α (δ ₀) (π₁ a) ﹐
   α (δ ₁) (π₁ (π₂ a)) ﹐
   Id-pop← Ω A δ (π₂ (π₂ a))
     (ap {Δ ▸ A} (λ x → α (pop x) (top x))
       (δ ∷ π₁ a ∷ π₁ (π₂ a) ∷ π₂ (π₂ a))) ﹐
   inl (π₁ a) ﹐ inl (π₁ (π₂ a)))

Id-β : {Δ : Tel} (Ω : el Δ → Type) {A B : el Δ → Type}
  (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
  (δ : el (ID Δ)) (b : Id-IDty B δ) → Id-Ω Ω {A} {B} α β δ
Id-β {Δ} Ω {A} {B} α β δ b =
  (β (δ ₀) (π₁ b) ﹐
   β (δ ₁) (π₁ (π₂ b)) ﹐
   Id-pop← Ω B δ (π₂ (π₂ b))
     (ap {Δ ▸ B} (λ x → β (pop x) (top x))
       (δ ∷ π₁ b ∷ π₁ (π₂ b) ∷ π₂ (π₂ b))) ﹐
   inr (π₁ b) ﹐ inr (π₁ (π₂ b)))

postulate
  ＝sum : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω)
    (ω : Ω) (u v : sum Ω α β ω) →
    (u ＝ v) ≡
    sum (＝Ω Ω α β) {＝IDty A} {＝IDty B} (＝α Ω α β) (＝β Ω α β)
        (ω ﹐ ω ﹐ refl ω ﹐ u ﹐ v)
  Id-sum : {Δ : Tel} (Ω : el Δ → Type) {A B : el Δ → Type}
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
    (ω : (x : el Δ) → Ω x) (δ : el (ID Δ))
    (u₀ : sum (Ω (δ ₀)) (α (δ ₀)) (β (δ ₀)) (ω (δ ₀)))
    (u₁ : sum (Ω (δ ₁)) (α (δ ₁)) (β (δ ₁)) (ω (δ ₁))) →
    Id (λ x → sum (Ω x) (α x) (β x) (ω x)) δ u₀ u₁ ≡
    sum (Id-Ω Ω α β δ) {Id-IDty A δ} {Id-IDty B δ}
        (Id-α Ω α β δ) (Id-β Ω α β δ)
        (ω (δ ₀) ﹐ ω (δ ₁) ﹐ ap ω δ ﹐ u₀ ﹐ u₁)

{-# REWRITE ＝sum Id-sum #-}

postulate
  refl-inl : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) (a : A) →
    refl (inl {Ω} {A} {B} {α} {β} a) ≡
    inl {＝Ω Ω α β} {＝IDty A} {＝IDty B} {＝α Ω α β} {＝β Ω α β} (a ﹐ a ﹐ refl a)
  refl-inr : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) (b : B) →
    refl (inr {Ω} {A} {B} {α} {β} b) ≡
    inr {＝Ω Ω α β} {＝IDty A} {＝IDty B} {＝α Ω α β} {＝β Ω α β} (b ﹐ b ﹐ refl b)
  ap-inl : {Δ : Tel} (δ : el (ID Δ)) (Ω A B : el Δ → Type)
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x) (a : (x : el Δ) → A x) →
    ap (λ x → inl {Ω x} {A x} {B x} {α x} {β x} (a x)) δ ≡
    coe→ (congᶠ (λ e → sum (Id-Ω Ω α β δ) {Id-IDty A δ} {Id-IDty B δ} (Id-α Ω α β δ) (Id-β Ω α β δ)
                           (α (δ ₀) (a (δ ₀)) ﹐ α (δ ₁) (a (δ ₁)) ﹐ e ﹐ inl (a (δ ₀)) ﹐ inl (a (δ ₁))))
               -- {ap {Δ ▸ A} (λ x → α (pop x) (top x)) (δ ∷ a (δ ₀) ∷ a (δ ₁) ∷ ap a δ)}
               -- {ap (λ z → α z (a z)) δ}
               (ap-AP {Δ} {Δ ▸ A} {λ z → Ω (pop z)} (λ x → x ∷ a x) (λ z → α (pop z) (top z)) δ))
      (inl {Id-Ω Ω α β δ} {Id-IDty A δ} {Id-IDty B δ}
           {Id-α Ω α β δ} {Id-β Ω α β δ}
           (a (δ ₀) ﹐ a (δ ₁) ﹐ ap a δ))
  ap-inr : {Δ : Tel} (δ : el (ID Δ)) (Ω A B : el Δ → Type)
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x) (b : (x : el Δ) → B x) →
    ap (λ x → inr {Ω x} {A x} {B x} {α x} {β x} (b x)) δ ≡
    coe→ (congᶠ (λ e → sum (Id-Ω Ω α β δ) {Id-IDty A δ} {Id-IDty B δ} (Id-α Ω α β δ) (Id-β Ω α β δ)
                           (β (δ ₀) (b (δ ₀)) ﹐ β (δ ₁) (b (δ ₁)) ﹐ e ﹐ inr (b (δ ₀)) ﹐ inr (b (δ ₁))))
               -- {ap {Δ ▸ B} (λ x → β (pop x) (top x)) (δ ∷ b (δ ₀) ∷ b (δ ₁) ∷ ap b δ)}
               -- {ap (λ z → β z (b z)) δ}
               (ap-AP {Δ} {Δ ▸ B} {λ z → Ω (pop z)} (λ x → x ∷ b x) (λ z → β (pop z) (top z)) δ))
      (inr {Id-Ω Ω α β δ} {Id-IDty A δ} {Id-IDty B δ}
           {Id-α Ω α β δ} {Id-β Ω α β δ}
           (b (δ ₀) ﹐ b (δ ₁) ﹐ ap b δ))
  ap-case : {Δ : Tel} (δ : el (ID Δ)) (Ω A B : el Δ → Type)
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
    (ω : (x : el Δ) → Ω x) (s : (x : el Δ) → sum (Ω x) (α x) (β x) (ω x))
    (C : (x : el Δ) (y : Ω x) → sum (Ω x) (α x) (β x) y → Type)
    (f : (x : el Δ) (a : A x) → C x (α x a) (inl a))
    (g : (x : el Δ) (b : B x) → C x (β x b) (inr b)) → 
    ap (λ x → case (ω x) (s x) (C x) (f x) (g x)) δ ≡
    coe→ (Id-AP {Δ} {Δ ▸ Ω ▸ (λ x → sum (Ω (pop x)) (α (pop x)) (β (pop x)) (top x))}
             (λ x → x ∷ ω x ∷ s x) δ
             (λ x → C (pop (pop x)) (top (pop x)) (top x))
             (case (ω (δ ₀)) (s (δ ₀)) (C (δ ₀)) (f (δ ₀)) (g (δ ₀)))
             (case (ω (δ ₁)) (s (δ ₁)) (C (δ ₁)) (f (δ ₁)) (g (δ ₁))))
     (case {Id-Ω Ω α β δ} {Id-IDty A δ} {Id-IDty B δ} {Id-α Ω α β δ} {Id-β Ω α β δ}
      (ω (δ ₀) ﹐ ω (δ ₁) ﹐ ap ω δ ﹐ s (δ ₀) ﹐ s (δ ₁)) (ap s δ)
      (λ y z → Id {Δ ▸ Ω ▸ λ x → sum (Ω (pop x)) (α (pop x)) (β (pop x)) (top x)}
                  (λ x → C (pop (pop x)) (top (pop x)) (top x))
                  (δ ∷ π₁ y ∷ π₁ (π₂ y) ∷ π₁ (π₂ (π₂ y)) ∷
                   π₁ (π₂ (π₂ (π₂ y))) ∷ π₂ (π₂ (π₂ (π₂ y))) ∷
                   coe→ {!!} z)
                  (case (π₁ y) (π₁ (π₂ (π₂ (π₂ y)))) (C (δ ₀)) (f (δ ₀)) (g (δ ₀)))
                  (case (π₁ (π₂ y)) (π₂ (π₂ (π₂ (π₂ y)))) (C (δ ₁)) (f (δ ₁)) (g (δ ₁))))
      (λ a → coe← {!?!}
        (ap {Δ ▸ A} (λ x → f (pop x) (top x))
            (δ ∷ π₁ a ∷ π₁ (π₂ a) ∷ π₂ (π₂ a))))
      (λ b → {!!}))
  refl-case : {Ω : Type} {A B : Type} {α : A → Ω} {β : B → Ω}
    (ω : Ω) (s : sum Ω α β ω)
    (C : (x : Ω) → sum Ω α β x → Type)
    (f : (a : A) → C (α a) (inl a)) (g : (b : B) → C (β b) (inr b)) →
    refl (case ω s C f g) ≡
    -- This may need a naturality coercion.  Let's do the ap version first.
    {!case {＝Ω Ω α β} {＝IDty A} {＝IDty B} {＝α Ω α β} {＝β Ω α β} (ω ﹐ ω ﹐ refl ω ﹐ s ﹐ s) (refl s)
        (λ x t → Id {ε ▸ (λ _ → Ω) ▸ (λ x → sum Ω α β (top x))} (λ y → C (top (pop y)) (top y))
                    ([] ∷ π₁ x ∷ π₁ (π₂ x) ∷ π₁ (π₂ (π₂ x)) ∷ π₁ (π₂ (π₂ (π₂ x))) ∷ π₂ (π₂ (π₂ (π₂ x))) ∷
                      coe→ (cong2 (λ p q → sum (＝Ω Ω α β) p q x)
                        (funext (λ a → ?))
                        (funext (λ b → ?)) t))
                    (case (π₁ x) (π₁ (π₂ (π₂ (π₂ x)))) C f g) (case (π₁ (π₂ x)) (π₂ (π₂ (π₂ (π₂ x)))) C f g))
        {!!} {!!}!}

{-# REWRITE refl-inl refl-inr ap-inl ap-inr #-}
