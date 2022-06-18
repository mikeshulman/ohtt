{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

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
Id : (A : Type) → A → A → Type
Id A a₀ a₁ = Id′ {Δ = ε} (λ _ → A) [] a₀ a₁
-}
-- then we couldn't rewrite Id′ of an arbitrary *constant* type family
-- to Id without producing infinite loops, since the above is also a
-- particular constant type family.  So instead we postulate Id
-- separately, along with the reduction for constant type families,
-- which has as a particular consequence that the above definitional
-- equality also holds.

postulate
  Id : (A : Type) → A → A → Type
  Id-const : {Δ : Tel} (A : Type) (δ : el (ID Δ)) (a₀ a₁ : A) →
    Id′ {Δ} (λ _ → A) δ a₀ a₁ ≡ Id A a₀ a₁

{-# REWRITE Id-const #-}

-- Similarly, reflexivity is nullary ap, with the same caveat.
postulate
  refl : {A : Type} (a : A) → Id A a a
  ap-const : {Δ : Tel} (A : Type) (δ : el (ID Δ)) (a : A) →
    ap {Δ} (λ _ → a) δ ≡ refl a

{-# REWRITE ap-const #-}

------------------------------
-- Reflexivity telescopes
------------------------------

-- Now we can define reflexivity for telescopes.
REFL : {Δ : Tel} (δ : el Δ) → el (ID Δ)

-- Like AP, we need to simultaneously prove that it respects ₀ and ₁
postulate
  REFL₀ : {Δ : Tel} (δ : el Δ) → (REFL δ)₀ ≡ δ
  REFL₁ : {Δ : Tel} (δ : el Δ) → (REFL δ)₁ ≡ δ

{-# REWRITE REFL₀ REFL₁ #-}

-- Moreover, in order to define REFL we'll also need to know its
-- analogue of Id′-AP, which in this case is something we can prove.
postulate
  Id′-REFL : {Δ : Tel} (A : el Δ → Type) (δ : el Δ) (a₀ : A ((REFL δ)₀)) (a₁ : A ((REFL δ)₁)) →
    Id′ A (REFL δ) a₀ a₁ ≡ Id (A δ) a₀ a₁

-- But in order to prove *that*, we'll also need to know that REFL is
-- the image of AP on constant terms.
  AP-const : {Δ : Tel} (Θ : Tel) (δ : el (ID Δ)) (t : el Θ) → AP {Δ} (λ _ → t) δ ≡ REFL t

{-# REWRITE Id′-REFL AP-const #-}

REFL {ε} δ = []
REFL {Δ ▸ A} (δ ∷ a) = REFL δ ∷ a ∷ a ∷ refl a


-- Rewriting along Id′-REFL and AP-const seems a bit more questionable
-- than along AP₀ and REFL₀, since they don't already reduce to reflᵉ
-- on arbitrary concrete telescopes, only on concrete telescopes of
-- concrete types.  However, given the way they're defined in terms of
-- each other, once we also make them both *be* reflᵉ as below, then I
-- believe the above definitions of them do *also* reduce to reflᵉ on
-- concrete telescopes.  Finally, this hasn't been a problem yet.


-- Id′-REFL-reflᵉ can't be a rewrite since its LHS reduces directly
-- rather than by case-analysis.  Instead we make the following a
-- rewrite, which in particular makes Id′-REFL-reflᵉ hold
-- definitionally.

Id′-AP-const : {Γ Δ : Tel} (f : el Δ) (γ : el (ID Γ)) (A : el Δ → Type) (a₀ a₁ : A f) →
  Id′-AP {Γ} (λ _ → f) γ A a₀ a₁ ≡ reflᵉ
Id′-AP-const f γ A a₀ a₁ = axiomK

{-# REWRITE Id′-AP-const #-}

-- The usefulness of having Id-REFL as a rewrite is limited in
-- practice, because if δ has internal structure, REFL will compute on
-- it, and can't be "un-rewritten" back to a REFL in order for Id-REFL
-- to fire.  So we still sometimes have to coerce along Id-REFL.  But
-- the fact that it is definitionally reflᵉ, at least on abstract
-- arguments, minimizes the effect of these coercions.

------------------------------
-- ap and reflexivity
------------------------------

-- Now we do the same for ap on reflexivity.
ap-REFL : {Δ : Tel} (A : el Δ → Type) (f : (δ : el Δ) → A δ) (δ : el Δ) →
  ap f (REFL δ) ≡ refl (f δ)
ap-REFL {Δ} A f δ = ≡ʰ→≡ (ap-AP {ε} (λ _ → δ) f [])

AP-REFL : {Δ Θ : Tel} (f : el Δ → el Θ) (δ : el Δ) →
  AP f (REFL δ) ≡ REFL (f δ)
AP-REFL f δ = AP-AP {ε} (λ _ → δ) f []

{-# REWRITE ap-REFL AP-REFL #-}

-- We can now assert that the functoriality rules for constant
-- families and functions reduce to reflexivity, which is well-typed
-- since both sides reduce to a homogeneous Id or a refl.
Id′-AP-CONST : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (A : Type) (a₀ a₁ : A) →
  Id′-AP f γ (λ _ → A) a₀ a₁ ≡ reflᵉ
Id′-AP-CONST f γ A a₀ a₁ = axiomK

{-# REWRITE Id′-AP-CONST #-}

ap-AP-CONST : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) {A : Type} (g : A) →
  ap-AP f (λ _ → g) γ ≡ reflʰ
ap-AP-CONST f γ g = axiomKʰ

AP-AP-CONST : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) {Θ : Tel} (g : el Θ) →
  AP-AP f (λ _ → g) γ ≡ reflᵉ
AP-AP-CONST f γ g = axiomK

{-# REWRITE ap-AP-CONST AP-AP-CONST #-}

-- The choice not to *define* Id, refl, and REFL as instances of Id′,
-- ap, and AP does mean that some of the rewrites we postulate for the
-- latter have to be given separately for the former in case the
-- latter get reduced to the former before these rules fire.

postulate
  REFL-pop : {Δ : Tel} (A : el Δ → Type) (δ : el (Δ ▸ A)) →
    REFL (pop δ) ≡ pop (pop (pop (REFL δ)))

{-# REWRITE REFL-pop #-}

top-pop-pop-REFL : {Δ : Tel} (A : el Δ → Type) (f : el (Δ ▸ A)) →
  top (pop (pop (REFL f))) ≡ top f
top-pop-pop-REFL A (δ ∷ a) = reflᵉ

top-pop-REFL : {Δ : Tel} (A : el Δ → Type) (f : el (Δ ▸ A)) →
  top (pop (REFL f)) ≡ top f
top-pop-REFL A (δ ∷ a) = reflᵉ

{-# REWRITE top-pop-pop-REFL top-pop-REFL #-}

-- Thus the only one thath needs to be postulated is refl-top.
postulate
  refl-top : (Δ : Tel) (A : el Δ → Type) (f : el (Δ ▸ A)) →
    refl (top f) ≡ coe← (Id′-AP {ε} {Δ} (λ _ → pop f) [] A (top f) (top f)) (top (REFL f)) 

{-# REWRITE refl-top #-}

-- The same is true for the specific type formers considered in other
-- files; all their rules for Id′ and ap have also to be given in
-- separate forms for Id and refl.
