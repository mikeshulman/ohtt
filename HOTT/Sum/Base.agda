{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Sum.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Unit
open import HOTT.Sigma.Base
open import HOTT.Indices

----------------------------------------
-- Sum types
----------------------------------------

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
  {ω : Ω} (s : sum Ω α β ω)
  (C : (x : Ω) → sum Ω α β x → Type)
  (f : (a : A) → C (α a) (inl a)) (g : (b : B) → C (β b) (inr b))
  → C ω s
case (inl a) C f g = f a
case (inr b) C f g = g b

_⊎_ : Type → Type → Type
A ⊎ B = sum ⊤ {A} {B} (λ _ → ★) (λ _ → ★) ★

----------------------------------------
-- Auxiliary stuff for Id-sum
----------------------------------------

＝Ω : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) → Type
＝Ω Ω α β = ＝Idx Ω (sum Ω α β)

＝α : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) → IDty A → ＝Ω Ω α β
＝α Ω {A} {B} α β z = ＝toIdx Ω (sum Ω α β) α inl z

＝β : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) → IDty B → ＝Ω Ω α β
＝β Ω {A} {B} α β z = ＝toIdx Ω (sum Ω α β) β inr z

Id-Ω : {Δ : Tel} (Ω : el Δ → Type) {A B : el Δ → Type}
  (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x) →
  (δ : el (ID Δ)) → Type
Id-Ω {Δ} Ω {A} {B} α β δ = Id-Idx δ Ω (λ x y → sum (Ω x) (α x) (β x) y)

-- TODO: Move this to HOTT.Indices
Id-Ω-pop : {Δ : Tel} (C : Δ ⇨ Type) (Ω : el Δ → Type) {A B : el Δ → Type}
  (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
  (δ : el (ID Δ)) (c₀ : C ⊘ (δ ₀)) (c₁ : C ⊘ (δ ₁)) (c₂ : Id C δ c₀ c₁) →
  Id-Ω Ω α β δ ≡
  Id-Ω (λ z₁ → Ω (pop {Δ} {C} z₁)) (λ z₁ z₂ → α (pop {Δ} {C} z₁) z₂)
    (λ z₁ z₂ → β (pop {Δ} {C} z₁) z₂)
    (δ ∷ c₀ ∷ c₁ ∷ c₂)
Id-Ω-pop {Δ} C Ω {A} {B} α β δ c₀ c₁ c₂ =
  ΣΣ≡Σ (Ω (δ ₀)) (Ω (δ ₁))
    (funextᵉ (λ x₀ → funextᵉ λ x₁ → rev (Id-AP (λ x → pop {B = C} x) (δ ∷ c₀ ∷ c₁ ∷ c₂) (Λ⇨ Ω) x₀ x₁)))
    (λ x₀ x₁ → Σ[ s₀ ﹕ sum (Ω (δ ₀)) (α (δ ₀)) (β (δ ₀)) x₀ ]
                        sum (Ω (δ ₁)) (α (δ ₁)) (β (δ ₁)) x₁)

Id-α : {Δ : Tel} (Ω : el Δ → Type) {A B : el Δ → Type}
  (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
  (δ : el (ID Δ)) (a : IDty′ A δ) → Id-Ω Ω {A} {B} α β δ
Id-α {Δ} Ω {A} {B} α β δ a =
  Id-toIdx δ Ω (λ x y → sum (Ω x) (α x) (β x) y) α (λ x y → inl y) a

Id-β : {Δ : Tel} (Ω : el Δ → Type) {A B : el Δ → Type}
  (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
  (δ : el (ID Δ)) (b : IDty′ B δ) → Id-Ω Ω {A} {B} α β δ
Id-β {Δ} Ω {A} {B} α β δ b =
  Id-toIdx δ Ω (λ x y → sum (Ω x) (α x) (β x) y) β (λ x y → inr y) b

postulate
  ＝sum : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω)
    (ω : Ω) (u v : sum Ω α β ω) →
    (u ＝ v) ≡
    sum (＝Ω Ω α β) {IDty A} {IDty B} (＝α Ω α β) (＝β Ω α β)
        (ω , ω , refl ω , u , v)
  Id-sum : {Δ : Tel} (Ω : el Δ → Type) {A B : el Δ → Type}
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
    (ω : (x : el Δ) → Ω x) (δ : el (ID Δ))
    (u₀ : sum (Ω (δ ₀)) (α (δ ₀)) (β (δ ₀)) (ω (δ ₀)))
    (u₁ : sum (Ω (δ ₁)) (α (δ ₁)) (β (δ ₁)) (ω (δ ₁))) →
    Id (Λ x ⇨ sum (Ω x) (α x) (β x) (ω x)) δ u₀ u₁ ≡
    sum (Id-Ω Ω α β δ) {IDty′ A δ} {IDty′ B δ}
        (Id-α Ω α β δ) (Id-β Ω α β δ)
        (ω (δ ₀) , ω (δ ₁) , ap (Λ⇨ Ω) ω δ , u₀ , u₁)

{-# REWRITE ＝sum Id-sum #-}

sum-pop : {Δ : Tel} (δ : el (ID Δ)) (Ω A B : el Δ → Type)
            (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
            (ω : (x : el Δ) → Ω x)
            (s : (x : el Δ) → sum (Ω x) (α x) (β x) (ω x))
            (C : (x : el Δ) (y : Ω x) → sum (Ω x) (α x) (β x) y → Type)
            (f : (x : el Δ) (a : A x) → C x (α x a) (inl a))
            (g : (x : el Δ) (b : B x) → C x (β x b) (inr b)) (y : Id-Ω Ω α β δ)
            (z : sum (Id-Ω Ω α β δ) (Id-α Ω α β δ) (Id-β Ω α β δ) y) →
          Id/ (Λ⇨ (λ x → sum (Ω (pop {Δ} {Λ⇨ Ω} x)) (α (pop x)) (β (pop x)) (top x))) ⊘
          δ ∷ fst y ∷ fst (snd y) ∷ fst (snd (snd y)) ∷
          fst (snd (snd (snd y))) ∷ snd (snd (snd (snd y)))
sum-pop {Δ} δ Ω A B α β ω s C f g y z =
  coe→ (sum≡
        {Id-Ω Ω α β δ}
        {Id-Ω (λ z₁ → Ω (pop {Δ} {Λ⇨ Ω} z₁)) (λ z₁ z₂ → α (pop z₁) z₂)
          (λ z₁ z₂ → β (pop z₁) z₂)
          (δ ∷ fst y ∷ fst (snd y) ∷ fst (snd (snd y)))}
        (Id-Ω-pop (Λ⇨ Ω) Ω α β δ (fst y) (fst (snd y)) (fst (snd (snd y))))
        {IDty′ A δ}
        (IDty′-pop (Λ⇨ Ω) A δ (fst y) (fst (snd y)) (fst (snd (snd y))))
        {IDty′ B δ}
        (IDty′-pop (Λ⇨ Ω) B δ (fst y) (fst (snd y)) (fst (snd (snd y))))
        {Id-α Ω α β δ}
        {Id-α (λ z₁ → Ω (pop {Δ} {Λ⇨ Ω} z₁)) (λ z₁ z₂ → α (pop z₁) z₂)
          (λ z₁ z₂ → β (pop z₁) z₂)
          (δ ∷ fst y ∷ fst (snd y) ∷ fst (snd (snd y)))}
        (funextʰ (λ a₀ a₁ a₂ → {!!}))
        {Id-β Ω α β δ}
        {Id-β (λ z₁ → Ω (pop {Δ} {Λ⇨ Ω} z₁)) (λ z₁ z₂ → α (pop z₁) z₂)
          (λ z₁ z₂ → β (pop z₁) z₂)
          (δ ∷ fst y ∷ fst (snd y) ∷ fst (snd (snd y)))}
        (funextʰ (λ b₀ b₁ b₂ → {!!}))
        {y}
        {fst y , fst (snd y) ,
          coe← (Id-AP (λ x → pop {B = Λ⇨ Ω} x) (δ ∷ fst y ∷ fst (snd y) ∷ fst (snd (snd y))) (Λ⇨ Ω) (fst y) (fst (snd y)))
               (fst (snd (snd y))) , snd (snd (snd y))}
        (,,≡ʰ, (funextᵉ (λ x₀ → funextᵉ λ x₁ → rev (Id-AP (λ x → pop {B = Λ⇨ Ω} x) (δ ∷ fst y ∷ fst (snd y) ∷ fst (snd (snd y))) (Λ⇨ Ω) x₀ x₁)))
          (fst y) (fst (snd y)) {fst (snd (snd y))}
          {coe← (Id-AP (λ x → pop {B = Λ⇨ Ω} x) (δ ∷ fst y ∷ fst (snd y) ∷ fst (snd (snd y))) (Λ⇨ Ω) (fst y) (fst (snd y))) (fst (snd (snd y)))}
          (revʰ (coe←≡ʰ (Id-AP (λ x → pop {B = Λ⇨ Ω} x) (δ ∷ fst y ∷ fst (snd y) ∷ fst (snd (snd y))) (Λ⇨ Ω) (fst y) (fst (snd y))) (fst (snd (snd y)))))
          (snd (snd (snd y)))))
        z

Id-C : {Δ : Tel} (δ : el (ID Δ)) (Ω A B : el Δ → Type)
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
    (ω : (x : el Δ) → Ω x) (s : (x : el Δ) → sum (Ω x) (α x) (β x) (ω x))
    (C : (x : el Δ) (y : Ω x) → sum (Ω x) (α x) (β x) y → Type)
    (f : (x : el Δ) (a : A x) → C x (α x a) (inl a))
    (g : (x : el Δ) (b : B x) → C x (β x b) (inr b))
    (y : Id-Ω Ω α β δ)
    (z : sum (Id-Ω Ω α β δ) (Id-α Ω α β δ) (Id-β Ω α β δ) y) →
    Type
Id-C {Δ} δ Ω A B α β ω s C f g y z =
  Id {Δ ▸ (Λ⇨ Ω) ▸ (Λ x ⇨ sum (Ω (pop x)) (α (pop x)) (β (pop x)) (top x))}
     (Λ x ⇨ C (pop (pop x)) (top (pop x)) (top x))
     (δ ∷ fst y ∷ fst (snd y) ∷ fst (snd (snd y)) ∷
      fst (snd (snd (snd y))) ∷ snd (snd (snd (snd y))) ∷
      sum-pop δ Ω A B α β ω s C f g y z)
     (case {ω = fst y} (fst (snd (snd (snd y)))) (C (δ ₀)) (f (δ ₀)) (g (δ ₀)))
     (case {ω = fst (snd y)} (snd (snd (snd (snd y)))) (C (δ ₁)) (f (δ ₁)) (g (δ ₁)))

postulate
  refl-inl : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) (a : A) →
    refl (inl {Ω} {A} {B} {α} {β} a) ≡
    inl {＝Ω Ω α β} {IDty A} {IDty B} {＝α Ω α β} {＝β Ω α β} (a , a , refl a)
  refl-inr : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) (b : B) →
    refl (inr {Ω} {A} {B} {α} {β} b) ≡
    inr {＝Ω Ω α β} {IDty A} {IDty B} {＝α Ω α β} {＝β Ω α β} (b , b , refl b)
  ap-inl : {Δ : Tel} (δ : el (ID Δ)) (Ω A B : el Δ → Type)
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
    (a : (x : el Δ) → A x) →
    ap (Λ x ⇨ sum (Ω x) (α x) (β x) (α x (a x)))
       (λ x → inl {Ω x} {A x} {B x} {α x} {β x} (a x)) δ ≡
    (inl {Id-Ω Ω α β δ} {IDty′ A δ} {IDty′ B δ}
         {Id-α Ω α β δ} {Id-β Ω α β δ}
         (a (δ ₀) , a (δ ₁) , ap (Λ⇨ A) a δ))
  ap-inr : {Δ : Tel} (δ : el (ID Δ)) (Ω A B : el Δ → Type)
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
    (b : (x : el Δ) → B x) →
    ap (Λ x ⇨ sum (Ω x) (α x) (β x) (β x (b x)))
       (λ x → inr {Ω x} {A x} {B x} {α x} {β x} (b x)) δ ≡
      (inr {Id-Ω Ω α β δ} {IDty′ A δ} {IDty′ B δ}
           {Id-α Ω α β δ} {Id-β Ω α β δ}
           (b (δ ₀) , b (δ ₁) , ap (Λ⇨ B) b δ))
  ap-case : {Δ : Tel} (δ : el (ID Δ)) (Ω A B : el Δ → Type)
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x)
    (ω : (x : el Δ) → Ω x) (s : (x : el Δ) → sum (Ω x) (α x) (β x) (ω x))
    (C : (x : el Δ) (y : Ω x) → sum (Ω x) (α x) (β x) y → Type)
    (f : (x : el Δ) (a : A x) → C x (α x a) (inl a))
    (g : (x : el Δ) (b : B x) → C x (β x b) (inr b)) → 
    ap (Λ x ⇨ C x (ω x) (s x))
       (λ x → case {ω = ω x} (s x) (C x) (f x) (g x)) δ ≡
    -- TODO: Bring back Id-AP≡ ?
    coe← (Id-AP {Δ} {Δ ▸ (Λ⇨ Ω) ▸ (Λ x ⇨ sum (Ω (pop x)) (α (pop x)) (β (pop x)) (top x))}
                (λ x → x ∷ ω x ∷ s x) δ (Λ x ⇨ C (pop (pop x)) (top (pop x)) (top x))
                (case {ω = ω (δ ₀)} (s (δ ₀)) (C (δ ₀)) (f (δ ₀)) (g (δ ₀)))
                (case {ω = ω (δ ₁)} (s (δ ₁)) (C (δ ₁)) (f (δ ₁)) (g (δ ₁)))
         •ᶠ {!!})
      (case {Id-Ω Ω α β δ} {IDty′ A δ} {IDty′ B δ} {Id-α Ω α β δ} {Id-β Ω α β δ}
        {ω (δ ₀) , ω (δ ₁) , ap (Λ⇨ Ω) ω δ , s (δ ₀) , s (δ ₁)}
        (ap (Λ x ⇨ sum (Ω x) (α x) (β x) (ω x)) s δ)
        (Id-C δ Ω A B α β ω s C f g)
        (λ a → {!ap (Λ x ⇨ C (pop x) (α (pop x) (top x)) (inl (top x))) (λ x → f (pop x) (top x)) (δ ∷ fst a ∷ fst (snd a) ∷ snd (snd a))!})
        (λ b → {!ap (Λ x ⇨ C (pop x) (β (pop x) (top x)) (inr (top x))) (λ x → g (pop x) (top x)) (δ ∷ fst b ∷ fst (snd b) ∷ snd (snd b))!}))
{-
  refl-case : {Ω : Type} {A B : Type} {α : A → Ω} {β : B → Ω}
    (ω : Ω) (s : sum Ω α β ω)
    (C : (x : Ω) → sum Ω α β x → Type)
    (f : (a : A) → C (α a) (inl a)) (g : (b : B) → C (β b) (inr b)) →
    refl (case {ω = ω} s C f g) ≡
    -- This may need a naturality coercion.  Let's do the ap version first.
    {!case {＝Ω Ω α β} {IDty A} {IDty B} {＝α Ω α β} {＝β Ω α β} {ω , ω , refl ω , s , s} (refl s)
        (λ x t → Id {ε ▸ (λ _ → Ω) ▸ (λ x → sum Ω α β (top x))} (λ y → C (top (pop y)) (top y))
                    ([] ∷ fst x ∷ fst (snd x) ∷ fst (snd (snd x)) ∷ fst (snd (snd (snd x))) ∷ snd (snd (snd (snd x))) ∷
                      coe→ (cong2 (λ p q → sum (＝Ω Ω α β) p q x)
                        (funext (λ a → ?))
                        (funext (λ b → ?)) t))
                    (case (fst x) (fst (snd (snd (snd x)))) C f g) (case (fst (snd x)) (snd (snd (snd (snd x)))) C f g))
        {!!} {!!}!}

-}

{-# REWRITE refl-inl refl-inr ap-inl ap-inr #-}
