{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Test where

open import HOTT.Rewrite hiding (rev)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Fill
open import HOTT.Groupoids
open import HOTT.Pi
open import HOTT.Sigma
open import HOTT.Copy
open import HOTT.Universe.Base
open import HOTT.Universe.Transport
open import HOTT.Universe.Top
open import HOTT.Universe.TopCompose
open import HOTT.Bool
open import HOTT.Univalence

----------------------------------------
-- Testing normalization of ap-top
----------------------------------------

postulate
  A : Type
  a₀ a₁ : A
  a₂ : a₀ ＝ a₁

postulate
  B : (ε▸ A) ⇨ Type
  b₀ : B ⊘ ([] ∷ a₀)
  b₁ : B ⊘ ([] ∷ a₁)
  b₂ : Id B ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁
  C : ((ε▸ A) ▸ B) ⇨ Type
  c₀ : C ⊘ ([] ∷ a₀ ∷ b₀)
  c₁ : C ⊘ ([] ∷ a₁ ∷ b₁)
  c₂ : Id C ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂) c₀ c₁

--Normalize these with C-c C-n
egA-A = ap {ε▸ A} ((Λ _ ⇨ A) ⊚ POP) (λ w → top w) ([] ∷ a₀ ∷ a₁ ∷ a₂)
egAB-A = ap {(ε▸ A) ▸ B} ((Λ _ ⇨ A) ⊚ POP ⊚ᵉ POP) (λ w → top (pop w)) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂)
egABC-A = ap {(ε▸ A) ▸ B ▸ C} ((Λ _ ⇨ A) ⊚ POP ⊚ᵉ POP ⊚ᵉ POP) (λ w → top (pop (pop w))) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂ ∷ c₀ ∷ c₁ ∷ c₂)
egAB-B = ap {(ε▸ A) ▸ B} (B ⊚ POP) (λ w → top w) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂)
egABC-B = ap {(ε▸ A) ▸ B ▸ C} (B ⊚ POP ⊚ᵉ POP) (λ w → top (pop w)) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂ ∷ c₀ ∷ c₁ ∷ c₂)
egABC-C = ap {(ε▸ A) ▸ B ▸ C} (C ⊚ POP) (λ w → top w) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂ ∷ c₀ ∷ c₁ ∷ c₂)

------------------------------
-- Definitional univalence
------------------------------

-- We check that both a function and its inverse are preserved
-- definitionally by passing through univalence.

coe⇒ua : {A B : Type} (f : A ⇒ B) (qf : isEquiv f) →
  coe⇒ (ua (f , qf)) ≡ f
coe⇒ua f qf = reflᵉ

coe⇐ua : {A B : Type} (f : A ⇒ B) (g : B ⇒ A)
  (sect : g ∘ f ＝ idmap A) (retr : f ∘ g ＝ idmap B) →
  coe⇐ (ua≋ (f , g , sect , retr)) ≡ g
coe⇐ua f g sect retr = reflᵉ

-- Furthermore, concatenation in the universe *almost* commutes with
-- coe⇒.  It only fails because of the lack of regularity:
-- concatenation is defined by filling a cubical horn with one side
-- being reflexivity, so coe⇒ on the concatenation must include
-- coercion backwards along that reflexivity.
coe⇨⊙ : {A B C : Type} (f : A ＝ B) (g : B ＝ C) (a : A) →
  coe⇒ (_⊙_ {Type} f g) ∙ a ≡ coe⇒ g ∙ (coe⇒ f ∙ (coe⇐ (refl A) ∙ a))
-- By the way, this is the reason we rearranged the components of
-- 11Corr: otherwise this computation would be infeasible.  This
-- way, the other components can be discarded quickly.
coe⇨⊙ f g a = reflᵉ

-- A similar thing happens with rev.
coe⇒rev : {A B : Type} (e : A ＝ B) (b : B) →
  coe⇒ (rev {Type} e) ∙ b ≡ coe⇒ (refl A) ∙ (coe⇒ (refl A) ∙ (coe⇐ e ∙ b))
coe⇒rev e b = reflᵉ

-- Instead of comp→, we could use utr→ to define a primitive notion of
-- "rev p ⊙ q":
_⁻¹⊙_ : {A : Type} {x y z : A} (p : x ＝ y) (q : x ＝ z) → y ＝ z
_⁻¹⊙_ {A} {x} {y} {z} p q = utr→ {ε} (Λ _ ⇨ A) [] x y z p q

-- But with our current definition of utr→Type in terms of filling,
-- this also computes with a refl in it.
coe⇨⁻¹⊙ : {A B C : Type} (f : A ＝ B) (g : A ＝ C) (b : B) →
  coe⇒ (_⁻¹⊙_ {Type} f g) ∙ b ≡ coe⇒ g ∙ (coe⇒ (refl A) ∙ (coe⇐ f ∙ b))
coe⇨⁻¹⊙ f g b = reflᵉ

-- We could probably give a different definition of utr→Type that
-- would compute coe⇒⊙′ without any refls.  But using ⊙′ in practice
-- would necessitate lots of rev's, and I can't think of any way to
-- define rev that doesn't get a refl: even using utr→ would involve
-- at least one refl.

-- The cheap way out would be to define a different notion of ⊙
-- specialized to the universe only, which demotes a pair of
-- identifications of types to equivalences, composes those, and then
-- promotes the composite back to an identification.  The somewhat
-- less cheap way out is to define a different notion of reflexivity
-- specialized to the universe, and then a specialized notion of
-- concatenation that only differs by using this special reflexivity.
-- This is what we did in Univalence when setting up equivalential
-- reasoning; it coerces without any refls.
coe⇨⊙U : {A B C : Type} (f : A ＝ B) (g : B ＝ C) (a : A) →
  coe⇒ (f ⊙U g) ∙ a ≡ coe⇒ g ∙ (coe⇒ f ∙ a)
coe⇨⊙U f g a = reflᵉ

-- But it's not fully satisfying, because we'd like to be able to use
-- the generic global operations like ⊙ on the universe, treating it
-- like any other type.  I don't know if there is a perfect solution
-- to this problem, short of finding a way to impose regularity.

------------------------------
-- Coercion along negation
------------------------------

-- We make the negation (flip) automorphism of bool into an
-- identification in the universe, and check that coercing along it
-- computes to the correct result.  This is some small amount of
-- evidence that we can hope for canonicity.

＝¬ : 𝟚 ＝ 𝟚
＝¬ = ua≋ (¬ , QInv-¬)

coe⇒¬ : coe⇒ ＝¬ ∙ true ≡ false
coe⇒¬ = reflᵉ

coe⇐¬ : coe⇐ ＝¬ ∙ true ≡ false
coe⇐¬ = reflᵉ
