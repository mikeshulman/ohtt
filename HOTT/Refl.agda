{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Refl where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

------------------------------
-- Homogeneous Id and refl
------------------------------

-- Homogeneous identity types are heterogeneous over the empty
-- telescope.  However, if we *defined* them to be that:
{-
_＝_ : (A : Type) → A → A → Type
(a₀ ＝ a₁) = Id {Δ = ε} (λ _ → A) [] a₀ a₁
-}
-- then we couldn't rewrite Id of an arbitrary *constant* type family
-- to _＝_ without producing infinite loops, since the above is also a
-- particular constant type family.  So instead we postulate _＝_
-- separately, along with the reduction for constant type families,
-- which has as a particular consequence that the above definitional
-- equality also holds.

postulate
  _＝_ : {A : Type} → A → A → Type
  Id-const : {Δ : Tel} (A : Type) (δ : el (ID Δ)) (a₀ a₁ : A) →
    Id {Δ} (λ _ → A) δ a₀ a₁ ≡ (a₀ ＝ a₁)

{-# REWRITE Id-const #-}

-- Similarly, reflexivity is nullary ap, with the same caveat.
postulate
  refl : {A : Type} (a : A) → (a ＝ a)
  ap-const : {Δ : Tel} (A : Type) (δ : el (ID Δ)) (a : A) →
    ap {Δ} (λ _ → a) δ ≡ refl a

{-# REWRITE ap-const #-}

------------------------------
-- Reflexivity telescopes
------------------------------

-- Now we can define reflexivity for telescopes.  Unlike for AP, this
-- doesn't require matching inside a λ, so we can make it an actual
-- definition instead of rewrite rules.
REFL : {Δ : Tel} (δ : el Δ) → el (ID Δ)

-- Like AP, we need to simultaneously postulate how REFL behaves on _₀
-- and _₁.
postulate
  REFL₀ : {Δ : Tel} (δ : el Δ) → (REFL δ)₀ ≡ᵉ δ
  REFL₁ : {Δ : Tel} (δ : el Δ) → (REFL δ)₁ ≡ᵉ δ

{-# REWRITE REFL₀ REFL₁ #-}

-- Moreover, to define REFL we'll also need to know its analogue of
-- Id-AP, and that REFL is the image of AP on constant terms.
postulate
  Id-REFL : {Δ : Tel} (A : el Δ → Type) (δ : el Δ) (a₀ : A δ) (a₁ : A δ) →
    Id A (REFL δ) a₀ a₁ ≡ (a₀ ＝ a₁)
  AP-const : {Δ : Tel} (Θ : Tel) (δ : el (ID Δ)) (t : el Θ) → AP {Δ} (λ _ → t) δ ≡ᵉ REFL t

{-# REWRITE Id-REFL AP-const #-}

REFL {ε} δ = []
REFL {Δ ▸ A} (δ ∷ a) = REFL δ ∷ a ∷ a ∷ refl a

postulate
  Id-[] : (A : el ε → Type) (a₀ : A []) (a₁ : A []) →
    Id A [] a₀ a₁ ≡ (a₀ ＝ a₁)

{-# REWRITE Id-[] #-}

-- As with Id-AP, if δ has internal structure, REFL will compute on
-- it, and can't be "un-rewritten" back to a REFL in order for
-- rewriting along Id-REFL to fire.  So we still sometimes have to
-- coerce along Id-REFL.  We also need some specialized version of
-- it, like for Id-AP.

postulate
  Id-REFL▸ : {Δ : Tel} (B : el Δ → Type) (A : el (Δ ▸ B) → Type) (δ : el Δ) (b : B δ)
    (a₀ : A ((REFL (_∷_ {Δ} {B} δ b))₀)) (a₁ : A ((REFL (_∷_ {Δ} {B} δ b))₁)) →
    Id A (REFL δ ∷ b ∷ b ∷ refl b) a₀ a₁ ≡ (a₀ ＝ a₁)
  Id-REFL[]▸ : (B : el ε → Type) (A : el (ε ▸ B) → Type) (b : B [])
    (a₀ : A (_∷_ {ε} {B} [] b)) (a₁ : A (_∷_ {ε} {B} [] b)) →
    Id A ([] ∷ b ∷ b ∷ refl b) a₀ a₁ ≡ (a₀ ＝ a₁)

{-# REWRITE Id-REFL▸ Id-REFL[]▸ #-}

postulate
  Id-REFL▸▸ : {Δ : Tel} (B : el Δ → Type) (C : el (Δ ▸ B) → Type)
    (A : el (Δ ▸ B ▸ C) → Type) (δ : el Δ) (b : B δ) (c : C (δ ∷ b))
    (a₀ : A (REFL (_∷_ {Δ ▸ B} {C} (_∷_ {Δ} {B} δ b) c)₀))
    (a₁ : A (REFL (_∷_ {Δ ▸ B} {C} (_∷_ {Δ} {B} δ b) c)₁)) →
    Id A (REFL δ ∷ b ∷ b ∷ refl b ∷ c ∷ c ∷ refl c) a₀ a₁ ≡ (a₀ ＝ a₁)

{-# REWRITE Id-REFL▸▸ #-}

Id-REFL▸-reflᵉ : {Δ : Tel} (B : el Δ → Type) (A : el (Δ ▸ B) → Type) (δ : el Δ) (b : B δ)
  (a₀ : A ((REFL (_∷_ {Δ} {B} δ b))₀)) (a₁ : A ((REFL (_∷_ {Δ} {B} δ b))₁)) →
  Id-REFL▸ B A δ b a₀ a₁ ≡ᵉ reflᵉ
Id-REFL▸-reflᵉ B A δ b a₀ a₁ = axiomK

Id-REFL[]▸-reflᵉ : (B : el ε → Type) (A : el (ε ▸ B) → Type) (b : B [])
  (a₀ : A (_∷_ {ε} {B} [] b)) (a₁ : A (_∷_ {ε} {B} [] b)) →
  Id-REFL[]▸ B A b a₀ a₁ ≡ᵉ reflᵉ
Id-REFL[]▸-reflᵉ B A b a₀ a₁ = axiomK

Id-REFL▸▸-reflᵉ : {Δ : Tel} (B : el Δ → Type) (C : el (Δ ▸ B) → Type)
  (A : el (Δ ▸ B ▸ C) → Type) (δ : el Δ) (b : B δ) (c : C (δ ∷ b))
  (a₀ : A (REFL (_∷_ {Δ ▸ B} {C} (_∷_ {Δ} {B} δ b) c)₀))
  (a₁ : A (REFL (_∷_ {Δ ▸ B} {C} (_∷_ {Δ} {B} δ b) c)₁)) →
  Id-REFL▸▸ B C A δ b c a₀ a₁ ≡ᵉ reflᵉ
Id-REFL▸▸-reflᵉ B C A δ b c a₀ a₁ = axiomK

{-# REWRITE Id-REFL▸-reflᵉ Id-REFL[]▸-reflᵉ Id-REFL▸▸-reflᵉ #-}

------------------------------
-- ap and reflexivity
------------------------------

ap-REFL : {Δ : Tel} (A : el Δ → Type) (f : (δ : el Δ) → A δ) (δ : el Δ) →
  ap f (REFL δ) ≡ refl (f δ)
ap-REFL {Δ} A f δ = (ap-AP {ε} (λ _ → δ) f [])

AP-REFL : {Δ Θ : Tel} (f : el Δ → el Θ) (δ : el Δ) →
  AP f (REFL δ) ≡ᵉ REFL (f δ)
AP-REFL f δ = AP-AP {ε} (λ _ → δ) f []

{-# REWRITE ap-REFL AP-REFL #-}

-- The choice not to *define* Id, refl, and REFL as instances of Id,
-- ap, and AP does mean that some of the rewrites we postulate for the
-- latter have to be given separately for the former in case the
-- latter get reduced to the former before these rules fire.

postulate
  REFL-pop : {Δ : Tel} (A : el Δ → Type) (δ : el (Δ ▸ A)) →
    REFL (pop δ) ≡ᵉ pop (pop (pop (REFL δ)))

{-# REWRITE REFL-pop #-}

postulate
  Id-AP-pop³-REFL : {Δ : Tel} (A B : el Δ → Type) (f : el (Δ ▸ B))
    (a₀ : A (pop f)) (a₁ : A (pop f)) →
    Id A (pop (pop (pop (REFL f)))) a₀ a₁ ≡ (a₀ ＝ a₁)

{-# REWRITE Id-AP-pop³-REFL #-}

top-pop-pop-REFL : {Δ : Tel} (A : el Δ → Type) (f : el (Δ ▸ A)) →
  top (pop (pop (REFL f))) ≡ top f
top-pop-pop-REFL A (δ ∷ a) = reflᵉ

top-pop-REFL : {Δ : Tel} (A : el Δ → Type) (f : el (Δ ▸ A)) →
  top (pop (REFL f)) ≡ top f
top-pop-REFL A (δ ∷ a) = reflᵉ

{-# REWRITE top-pop-pop-REFL top-pop-REFL #-}

-- Thus the only one that needs to be postulated is refl-top.
postulate
  refl-top : (Δ : Tel) (A : el Δ → Type) (f : el (Δ ▸ A)) →
    refl (top f) ≡ top (REFL f)

{-# REWRITE refl-top #-}

-- The same is true for the specific type formers considered in other
-- files; all their rules for Id and ap have also to be given in
-- separate forms for Id and refl.
