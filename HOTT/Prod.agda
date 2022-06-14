{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Prod where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport

--------------------
-- Product types
--------------------

-- It may seem that we should derive these from Σ-types, but various
-- things simplify in the non-dependent case, so I think it's worth
-- defining them separately.

postulate
  _×_ : Type → Type → Type
  _,_ : {A : Type} {B : Type} → A → B → A × B
  fst : {A : Type} {B : Type} → A × B → A
  snd : {A : Type} {B : Type} → A × B → B

infix 30 _×_

postulate
  βfst : (A : Type) (B : Type) (a : A) (b : B) → fst (a , b) ≡ a
  βsnd : (A : Type) (B : Type) (a : A) (b : B) → snd (a , b) ≡ b
  η, : (A : Type) (B : Type) (u : A × B) → (fst u , snd u) ≡ u
  Id× : (A B : Type) (u v : A × B) →
    Id (A × B) u v ≡ Id A (fst u) (fst v) × Id B (snd u) (snd v)
  Id′× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u : A (δ ₀) × B (δ ₀)) (v : A (δ ₁) × B (δ ₁)) →
    Id′ (λ w → A w × B w) δ u v ≡ Id′ A δ (fst u) (fst v) × Id′ B δ (snd u) (snd v)

{-# REWRITE βfst βsnd η, Id× Id′× #-}

postulate
  ap, : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (f : (x : el Δ) → A x) (g : (x : el Δ) → B x) →
    ap (λ x → (f x , g x)) δ ≡ (ap f δ , ap g δ)
  ap-fst : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (f : (x : el Δ) → A x × B x) →
    ap (λ x → fst (f x)) δ ≡ fst (ap f δ)
  ap-snd : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (f : (x : el Δ) → A x × B x) →
    ap (λ x → snd (f x)) δ ≡ snd (ap f δ)
  refl, : {A B : Type} (a : A) (b : B) → refl (a , b) ≡ (refl a , refl b)
  refl-fst : {A B : Type} (u : A × B) → refl (fst u) ≡ fst (refl u)
  refl-snd : {A B : Type} (u : A × B) → refl (snd u) ≡ snd (refl u)

{-# REWRITE ap, ap-fst ap-snd refl, refl-fst refl-snd #-}

postulate
  Id′-AP× : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ))
           (A B : el Δ → Type) {u₀ : A (f (γ ₀)) × B (f (γ ₀))} {u₁ : A (f (γ ₁)) × B (f (γ ₁))} →
    Id′-AP f γ (λ w → A w × B w) u₀ u₁ ≡ cong2 _×_ (Id′-AP f γ A (fst u₀) (fst u₁)) (Id′-AP f γ B (snd u₀) (snd u₁))

{-# REWRITE Id′-AP× #-}

postulate
  ap-AP, : {Γ Δ : Tel} {A B : el Δ → Type} (f : el Γ → el Δ) (g : (x : el Δ) → A x) (h : (x : el Δ) → B x) (γ : el (ID Γ)) →
    ap-AP f (λ x → (g x , h x)) γ ≡
    let p = rev (Id′-AP f γ A (g (f (γ ₀))) (g (f (γ ₁)))) in
    let q = rev (Id′-AP f γ B (h (f (γ ₀))) (h (f (γ ₁)))) in
    cong2ʰ (≡Type→≡ᵉ p) (≡Type→≡ᵉ q) (≡Type→≡ᵉ (cong2 _×_ p q))
           (scong2ʰ (λ A B → _,_ {A} {B}) p q) (ap-AP f g γ) (ap-AP f h γ)
  ap-AP-fst : {Γ Δ : Tel} {A B : el Δ → Type} (f : el Γ → el Δ) (g : (x : el Δ) → A x × B x) (γ : el (ID Γ)) →
    ap-AP f (λ x → fst (g x)) γ ≡
    let p = rev (Id′-AP f γ A (fst (g (f (γ ₀)))) (fst (g (f (γ ₁))))) in
    let q = rev (Id′-AP f γ B (snd (g (f (γ ₀)))) (snd (g (f (γ ₁))))) in
    congʰ (≡Type→≡ᵉ (cong2 _×_ p q)) (≡Type→≡ᵉ p) (scong2ʰ (λ A B → fst {A} {B}) p q) (ap-AP f g γ) 
  ap-AP-snd : {Γ Δ : Tel} {A B : el Δ → Type} (f : el Γ → el Δ) (g : (x : el Δ) → A x × B x) (γ : el (ID Γ)) →
    ap-AP f (λ x → snd (g x)) γ ≡
    let p = rev (Id′-AP f γ A (fst (g (f (γ ₀)))) (fst (g (f (γ ₁))))) in
    let q = rev (Id′-AP f γ B (snd (g (f (γ ₀)))) (snd (g (f (γ ₁))))) in
    congʰ (≡Type→≡ᵉ (cong2 _×_ p q)) (≡Type→≡ᵉ q) (scong2ʰ (λ A B → snd {A} {B}) p q) (ap-AP f g γ) 

{-# REWRITE ap-AP, ap-AP-fst ap-AP-snd #-}

----------------------------------------
-- Transport in product types
----------------------------------------

postulate
  tr→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₀ : A (δ ₀) × B (δ ₀)) →
    tr→ (λ w → A w × B w) δ u₀ ≡ (tr→ A δ (fst u₀) , tr→ B δ (snd u₀))
  tr←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₁ : A (δ ₁) × B (δ ₁)) →
    tr← (λ w → A w × B w) δ u₁ ≡ (tr← A δ (fst u₁) , tr← B δ (snd u₁))

{-# REWRITE tr→× tr←× #-}

postulate
  lift→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₀ : A (δ ₀) × B (δ ₀)) →
    lift→ (λ w → A w × B w) δ u₀ ≡ (lift→ A δ (fst u₀) , lift→ B δ (snd u₀))
  lift←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₁ : A (δ ₁) × B (δ ₁)) →
    lift← (λ w → A w × B w) δ u₁ ≡ (lift← A δ (fst u₁) , lift← B δ (snd u₁))

{-# REWRITE lift→× lift←× #-}

postulate
  utr→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : A (δ ₀) × B (δ ₀)) (u₁ u₁' : A (δ ₁) × B (δ ₁))
    (u₂ : Id′ (λ w → A w × B w) δ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ u₀ u₁') →
    utr→ (λ w → A w × B w) δ u₀ u₁ u₁' u₂ u₂' ≡
    (utr→ A δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') , utr→ B δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂'))
  utr←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : A (δ ₁) × B (δ ₁)) (u₀ u₀' : A (δ ₀) × B (δ ₀))
    (u₂ : Id′ (λ w → A w × B w) δ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ u₀' u₁) →
    utr← (λ w → A w × B w) δ u₁ u₀ u₀' u₂ u₂' ≡
    (utr← A δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') , utr← B δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂'))

{-# REWRITE utr→× utr←× #-}

postulate
  ulift→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : A (δ ₀) × B (δ ₀)) (u₁ u₁' : A (δ ₁) × B (δ ₁))
    (u₂ : Id′ (λ w → A w × B w) δ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ u₀ u₁') →
    ulift→ (λ w → A w × B w) δ u₀ u₁ u₁' u₂ u₂' ≡
    (coe← (Id′-AP {ε ▸ (λ _ → A (δ ₁) × B (δ ₁))} {ε ▸ (λ _ → A (δ ₁))} (λ w → (pop w ∷ fst (top w)))
                  ([] ∷ u₁ ∷ u₁' ∷ (utr→ A δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') ,
                                    utr→ B δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
                  (λ w → Id′ A δ (fst u₀) (top w)) (fst u₂) (fst u₂'))
          (ulift→ A δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂')) ,
     coe← (Id′-AP {ε ▸ (λ _ → A (δ ₁) × B (δ ₁))} {ε ▸ (λ _ → B (δ ₁))} (λ w → (pop w ∷ snd (top w)))
                  ([] ∷ u₁ ∷ u₁' ∷ (utr→ A δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') ,
                                    utr→ B δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
                  (λ w → Id′ B δ (snd u₀) (top w)) (snd u₂) (snd u₂'))
          (ulift→ B δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
  ulift←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : A (δ ₁) × B (δ ₁)) (u₀ u₀' : A (δ ₀) × B (δ ₀))
    (u₂ : Id′ (λ w → A w × B w) δ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ u₀' u₁) →
    ulift← (λ w → A w × B w) δ u₁ u₀ u₀' u₂ u₂' ≡
    (coe← (Id′-AP {ε ▸ (λ _ → A (δ ₀) × B (δ ₀))} {ε ▸ (λ _ → A (δ ₀))} (λ w → (pop w ∷ fst (top w)))
                  ([] ∷ u₀ ∷ u₀' ∷ (utr← A δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') ,
                                    utr← B δ (snd u₁) (snd u₀) (snd u₀') (snd u₂)  (snd u₂')))
                  (λ w → Id′ A δ (top w) (fst u₁)) (fst u₂) (fst u₂'))
          (ulift← A δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂')) ,
     coe← (Id′-AP {ε ▸ (λ _ → A (δ ₀) × B (δ ₀))} {ε ▸ (λ _ → B (δ ₀))} (λ w → (pop w ∷ snd (top w)))
                  ([] ∷ u₀ ∷ u₀' ∷ (utr← A δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') ,
                                    utr← B δ (snd u₁) (snd u₀) (snd u₀') (snd u₂)  (snd u₂')))
                  (λ w → Id′ B δ (top w) (snd u₁)) (snd u₂) (snd u₂'))
          (ulift← B δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂')))

{-# REWRITE ulift→× ulift←× #-}
