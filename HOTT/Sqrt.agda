{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Sqrt where

open import HOTT.Base
open import HOTT.Id
-- The definition of √ is in the Universe file, since it requires Id
-- and is required for the universe.
open import HOTT.Universe public
open import HOTT.Square.Simple

------------------------------
-- Identifications in √
------------------------------

√′-I : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type) → Type
√′-I {I} A = （ i₀ ⦂ I ）× （ i₁ ⦂ I ）× （ i₂ ⦂ i₀ ＝ i₁ ）× √ A i₀ × √ A i₁

√′-A : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type) →
  (u₀ u₁ : √′-I A) (u₂ : u₀ ＝ u₁) → Type
√′-A {I} A u₀ u₁ u₂ =
  Id {ID I} (λ iₓ → A (₁st iₓ) (₂nd iₓ) (₃rd' iₓ))
    {₁st u₀ , ₁st u₁ , ₁st u₂} {₂nd u₀ , ₂nd u₁ , ₂nd u₂}
    -- NB: There is a symmetry here!
    (₃rd u₀ , ₃rd u₁ , sym I ┌─     ₂nd u₂     ─┐
                             ₃rd u₀   □    ₃rd u₁
                             └─     ₁st u₂     ─┘  (₃rd u₂))
    (dig {I} {A} {₁st u₀} {₁st u₁} {₁st u₂} {₄th u₀} {₄th u₁}
         (←Id-ap {（ z ⦂ I × I ）× fst z ＝ snd z} {I} (λ z → fst (fst z)) (𝛌 (√ A))
                 {(₁st u₀ , ₂nd u₀) , ₃rd u₀} {(₁st u₁ , ₂nd u₁) , ₃rd u₁} ((₁st u₂ , ₂nd u₂) , ₃rd u₂)
                 (₄th u₂)))
    (dig {I} {A} {₂nd u₀} {₂nd u₁} {₂nd u₂} {₅th' u₀} {₅th' u₁}
         (←Id-ap {（ w ⦂ （ z ⦂ I × I ）× fst z ＝ snd z ）× √ A (fst (fst w))} {I} (λ z → snd (fst (fst z))) (𝛌 (√ A))
                 {((₁st u₀ , ₂nd u₀) , ₃rd u₀) , ₄th u₀} {((₁st u₁ , ₂nd u₁) , ₃rd u₁) , ₄th u₁} (((₁st u₂ , ₂nd u₂) , ₃rd u₂) , ₄th u₂)
                 (₅th' u₂)))

postulate
  ＝-√ : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type} (i : I) (s₀ s₁ : √ A i) →
    (s₀ ＝ s₁) ≡
    A i i (refl i) × √ {√′-I A} (√′-A A) (i , i , refl i , s₀ , s₁)
  Id-√ : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {Δ : Type} (i : Δ → I) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (s₀ : √ A (i δ₀)) (s₁ : √ A (i δ₁)) →
    Id (λ δ → √ A (i δ)) δ₂ s₀ s₁ ≡
    A (i δ₀) (i δ₁) (ap i δ₂) × √ {√′-I A} (√′-A A) (i δ₀ , i δ₁ , ap i δ₂ , s₀ , s₁)
{-# REWRITE ＝-√ Id-√ #-}

------------------------------
-- Dig vs fst
------------------------------

-- Once we have the computation rules for identifications in √ as a
-- cartesian product, we can see that "dig" is really just the
-- projection "fst" to the first component.  Under this
-- characterization, the specification of the first components in
-- refl-bury and ap-bury are what implement the β-rule for √, meaning
-- the value of dig (i.e. fst) composed with ap-bury.

-- Unfortunately, declaring dig≡fst as a rewrite causes normalization
-- loops in anything of the form (A₂ ↓).  I think the problem is that
-- the fst that dig normalizes to has both types in the × of Id-√ as
-- parameters, but the second one includes some digs in √′-A.  Thus,
-- fully normalizing it ends up rewriting those digs to fsts, and so
-- on forever.

-- A possibly-ideal solution would be for Agda to implement rewriting
-- that matches on record projections.  Then our Σ could be a record
-- and fst wouldn't have parameters.

-- Lacking that, the best option I've thought of so far is to not make
-- dig≡fst a rewrite at all, but just coerce across it when necessary.
postulate
  dig≡fst : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {i₀ i₁ : I} {i₂ : i₀ ＝ i₁} {s₀ : √ A i₀} {s₁ : √ A i₁} (s₂ : Id (√ A) i₂ s₀ s₁) →
    dig {I} {A} {i₀} {i₁} {i₂} {s₀} {s₁} s₂ ≡ fst s₂

-- We reduce the impact of this by *also* asserting dig-refl-bury and
-- dig-ap-bury directly as rewrites.  This will hopefully allow making
-- the equality dig≡fst rewrite to reflᵉ when applied to an ap-bury,
-- so that coercions disappear in most concrete cases.  In addition,
-- these rewrites seem to be necessary in order for the general
-- refl-bury and ap-bury rules below to be well-typed.

postulate
  dig-refl-bury : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂)) (k : K) →
    dig (refl (bury A j d k)) ≡ d k k (refl k)
{-# REWRITE dig-refl-bury #-}

-- For the types to match in dig-ap-bury, we need ap-ap functoriality
-- for j and k.  We can make this happen definitionally by wrapping
-- one of them in a ⇒.
frob-dig-ap-bury : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type)
  {@♭ K : Type} (@♭ j : K ⇒ I)
  (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j ∙ k₀) (j ∙ k₁) (ap (j ∙_) k₂))
  {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (k : Δ → K) →
  A (j ∙ k δ₀) (j ∙ k δ₁) (ap (λ z → j ∙ k z) δ₂)
frob-dig-ap-bury {I} A {K} j d {Δ} {δ₀} {δ₁} δ₂ k = d (k δ₀) (k δ₁) (ap k δ₂)

postulate
  dig-ap-bury : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂))
    {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (k : Δ → K) →
    dig (ap (λ δ → bury A j d (k δ)) δ₂) ≡ frob-dig-ap-bury A (𝛌 j) d δ₂ k
{-# REWRITE dig-ap-bury #-}

------------------------------
-- Computation in √
------------------------------

-- Because √ semantically has a strict universal property, it makes
-- sense to compute refl-bury and ap-bury to pairs whose second
-- components are actual "bury"s for √′.

postulate
  refl-bury : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂)) (k : K) →
    refl (bury A j d k) ≡
    (d k k (refl k) ,
     bury (√′-A A) (λ k → (j k , j k , refl (j k) , bury A j d k , bury A j d k))
       (λ k₀ k₁ k₂ → refl (d k₀ k₁ k₂))
       k)
{-# REWRITE refl-bury #-}

{-
frob-ap-bury : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type)
  {@♭ K : Type} (@♭ j : K ⇒ I)
  (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j ∙ k₀) (j ∙ k₁) (ap (j ∙_) k₂))
  {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (k : Δ → K) →
  (A (j ∙ k δ₀) (j ∙ k δ₁) (ap (λ z → j ∙ k z) δ₂)) ×
  √ (√′-A (λ i₂ i₁ i₀ → A i₂ i₁ i₀))
    (j ∙ k δ₀ , j ∙ k δ₁ , ap (λ z → j ∙ k z) δ₂ , bury A (j ∙_) d (k δ₀) , bury A (j ∙_) d (k δ₁))
frob-ap-bury {I} A {K} j d {Δ} {δ₀} {δ₁} δ₂ k =
  (d (k δ₀) (k δ₁) (ap k δ₂) ,
   bury (√′-A A) {ID K} (λ kₓ → (j ∙ ₁st kₓ , j ∙ ₂nd kₓ , ap (j ∙_) (₃rd' kₓ) , bury A (j ∙_) d (₁st kₓ) , bury A (j ∙_) d (₂nd kₓ)))
     (λ k₀ k₁ k₂ → {!dig (ap (λ x → ap (bury A (j ∙_) d) (₃rd' x)) k₂)!})
     (k δ₀ , k δ₁ , ap k δ₂))

postulate
  ap-bury : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂))
    {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (k : Δ → K) →
    ap (λ δ → bury A j d (k δ)) δ₂ ≡ frob-ap-bury A (𝛌 j) d δ₂ k
--{-# REWRITE ap-bury #-}
-}

------------------------------
-- Reducing dig≡fst
------------------------------

-- Since now refl-bury reduces directly, the previous rewrite
-- dig-refl-bury doesn't fire any more, so we restate it applying to
-- the reduced version of refl-bury.
postulate
  dig-refl-bury' : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂)) (k : K) →
    dig (d k k (refl k) ,
     bury (√′-A A) (λ k → (j k , j k , refl (j k) , bury A j d k , bury A j d k))
       (λ k₀ k₁ k₂ → refl (d k₀ k₁ k₂))
       k) ≡ d k k (refl k)
--- For some reason this REWRITE pragma seems to spin forever.
--{-# REWRITE dig-refl-bury' #-}

{-
postulate
  dig≡fst-refl-bury : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type)
    {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂)) (k : K) →
    dig≡fst (refl (bury A j d k)) ≡ᵉ {!reflᵉ!}
-}

