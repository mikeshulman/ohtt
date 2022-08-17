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
  refl-ƛ : (A : Type) (B : A → Type) (f : (x : A) → B x) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    refl (𝛌 f) ∙ a₀ ∙ a₁ ∙ a₂ ≡
    {!refl {（ x ⦂ (ε ▸ (Λ _ ⇨ A)) ）⇨ B (top x)} (Λ x ⇨ f (top x)) ⊘ ([] ∷ a₀ ∷ a₁ ∷ a₂)!}
  ap-ƛ : (Δ : Tel) (A : el Δ → Type) (B : (x : el Δ) → A x → Type)
    (f : (x : el Δ) → (y : A x) → B x y) →
    refl (Λ x ⇨ 𝛌 (f x)) ≡ Λ δ ⇨ ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒
    refl (Λ y ⇨ f (pop y) (top y)) ⊘ (δ ∷ a₀ ∷ a₁ ∷ a₂)

{-
LHS of refl-ƛⁿᵈ is:

_∙_ {_＝_ {A} a₀ a₁} {λ x → _＝_ {B} (f a₀) (f a₁)}
 (_∙_ {A} {λ a₃ → _＝_ {A} a₀ a₃ ⇒ _＝_ {B} (f a₀) (f a₃)}
  (_∙_ {A}
   {λ a₃ → Π A (λ a₄ → _＝_ {A} a₃ a₄ ⇒ _＝_ {B} (f a₃) (f a₄))}
   (refl {Π A (λ _ → B)} (𝛌 {A} {λ _ → B} f)) a₀)
  a₁)
 a₂

Goal of refl-λ is:

_∙_ {_＝_ {A} a₀ a₁} {λ x → B a₀ ＝U B a₁}
      (_∙_ {A} {λ a₃ → _＝_ {A} a₀ a₃ ⇒ (B a₀ ＝U B a₃)}
       (_∙_ {A} {λ a₃ → Π A (λ a₄ → _＝_ {A} a₃ a₄ ⇒ (B a₃ ＝U B a₄))}
        (refl {Π A (λ x → Type)} (𝛌 {A} {λ x → Type} B)) a₀)
       a₁)
      a₂

      // f a₀ ~ f a₁

I think it doesn't match because ＝U is not actually an equality type.
This is the "rewriting green slime" problem.  Surprisingly, it doesn't
seem to come up much elsewhere in this development. -}


{-
{-# REWRITE refl-ƛ ap-ƛ #-}

{-
Ah, I see the problem.  Applying (refl f) to an argument forces its
type to be computed; C-u C-u C-c C-. on (refl f) also triggers the
problem.  Computing this type, by ＝Π, yields a function type whose
codomain is (Id (𝛌 B)).  Applying the definition of Id, this becomes
(refl (𝛌 B)), or more precisely (refl (𝛌 {A} {Type} B)).  But refl-ƛ
then computes this to something involving (Id (ƛ _ ⇒ Type)), and we're
in a cycle.

The above fix of refl-ƛ, which reduces only when applied to all of its
arguments, appears to solve this problem, at least where we've
encountered it so far.  But a similar change made to refl-ƛⁿᵈ in
Pi.agda causes refl-ƛ itself to not typecheck!  I don't know why yet.

-}

frob-ap-∙ⁿᵈ : {Δ : Tel} (A B : Δ ⇨ Type)
    (f : (x : el Δ) → A ⊘ x ⇒ B ⊘ x) (a : (x : el Δ) → A ⊘ x)
    (δ : el (ID Δ)) →
    𝕀𝕕 B δ (f (δ ₀) ∙ a (δ ₀)) (f (δ ₁) ∙ a (δ ₁))
frob-ap-∙ⁿᵈ A B f a δ =
  refl (𝚲 f) ⊘ δ ∙ a (δ ₀) ∙ a (δ ₁) ∙ (refl (𝚲 a) ⊘ δ)

postulate
  ap-∙ⁿᵈ : {Δ : Tel} (A B : el Δ → Type)
    (f : (x : el Δ) → A x ⇒ B x) (a : (x : el Δ) → A x) →
    refl (Λ x ⇨ f x ∙ a x) ≡ Λ δ ⇨ frob-ap-∙ⁿᵈ (𝚲 A) (𝚲 B) f a δ

{-# REWRITE ap-∙ⁿᵈ #-}

{-
frob-refl-∙ : {A : Type} (B : A ⇒ Type) (f : Π A (B ∙_)) (a : A) →
  f ∙ a ＝ f ∙ a
frob-refl-∙ B f a = {!!}
-}

{-
postulate
  refl-∙ : (A : Type) (B : A → Type) (f : Π A B) (a : A) →
    refl (f ∙ a) ≡ {!!}
-}
{-
  ap-∙ : {Δ : Tel} (A : el Δ → Type) (B : (x : el Δ) → A x → Type)
    (f : (x : el Δ) → Π (A x) (B x)) (a : (x : el Δ) → A x) (δ : el (ID Δ)) →
    refl (Λ x ⇨ f x ∙ a x) ≡ ?
-}

----------------------------------------
-- Identity types of eliminators
----------------------------------------

-- Since refl//~ computes to ＝ rather than vice versa, we need to
-- assert the computation rules that would apply to refl also for ＝.
-- Since Type has no introduction forms, this just means eliminators.

postulate
  ＝∙ : (A : Type) (B : A ⇒ Type) (a : A) (b₀ b₁ : B ∙ a) →
    (b₀ ＝ b₁) ≡ refl B ∙ a ∙ a ∙ refl a // b₀ ~ b₁ 

{-# REWRITE ＝∙ #-}
-}
