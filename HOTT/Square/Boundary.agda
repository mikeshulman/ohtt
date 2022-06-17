{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Square.Boundary where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base

------------------------------
-- Boundary frobnification
------------------------------

-- It turns out that most of the boundary can be used without
-- modification, but we need to frobnicate the types of a₀₂ and a₁₂.
frob₀₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁) →
  Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁
frob₀₂ {Δ} A δ {a₀₀} {a₀₁} a₀₂ = coe← (Id′-AP (_₀ {Δ}) δ A a₀₀ a₀₁) a₀₂

unfrob₀₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁) →
  Id′ A (δ ₀₂) a₀₀ a₀₁
unfrob₀₂ {Δ} A δ {a₀₀} {a₀₁} a₀₂ = coe→ (Id′-AP (_₀ {Δ}) δ A a₀₀ a₀₁) a₀₂

frob₀₂≡ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁) →
  frob₀₂ A δ a₀₂ ≡ʰ a₀₂
frob₀₂≡ {Δ} A δ {a₀₀} {a₀₁} a₀₂ = coe←≡ʰ (Id′-AP (_₀ {Δ}) δ A a₀₀ a₀₁) a₀₂

unfrob₀₂≡ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁) →
  unfrob₀₂ A δ a₀₂ ≡ʰ a₀₂
unfrob₀₂≡ {Δ} A δ {a₀₀} {a₀₁} a₀₂ = coe→≡ʰ (Id′-AP (_₀ {Δ}) δ A a₀₀ a₀₁) a₀₂

frob-unfrob₀₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁) →
  frob₀₂ A δ (unfrob₀₂ A δ a₀₂) ≡ a₀₂
frob-unfrob₀₂ A δ {a₀₀} {a₀₁} a₀₂ = coe←coe→ (Id′-AP _₀ δ A a₀₀ a₀₁)

unfrob-frob₀₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁) →
  unfrob₀₂ A δ (frob₀₂ A δ a₀₂) ≡ a₀₂
unfrob-frob₀₂ A δ {a₀₀} {a₀₁} a₀₂ = coe→coe← (Id′-AP _₀ δ A a₀₀ a₀₁)

-- Unfortunately, it doesn't seem to work to make frob-unfrob and
-- unfrob-frob into rewrites.  (It does work if we make frob and
-- unfrob postulates, but then they wouldn't reduce away on concrete
-- types.)  So we have to coerce along them explicitly.  At least,
-- with the concrete definitions we have given, they should also
-- reduce automatically to reflᵉ on concrete types.

-- There is a potential way to make frob-unfrob and unfrob-frob hold
-- definitionally: if we augmented Id′-AP and Id′-AP≡ by explicit
-- functions that "coerce" along them, and heterogeneous equalities
-- for these "coercions", which are all computed type-wise in the same
-- way.  The Id′-AP≡ coercions would reduce over refls to the Id′-AP
-- ones, just as the equalities do, and we would also postulate
-- heterogeneous equalities between these "coercions" and their inputs
-- which satisfy some triangle identities.  Finally, we could also
-- assert by a rewrite that the two "coercions" are definitionally
-- inverse.  I tried this, and it worked to simplify the definition of
-- top₂₂ to just (top δ).  However, it seemed unlikely to greatly
-- simplify later problems such as SYM-SYM, and would require a *lot*
-- more boilerplate for each type former (computation of four
-- coercions and four heterogeneous equalities), so I've dropped the
-- idea for now.

-- When frobnicating a₁₂, note that we need a₀₂ as an explicit argument.
frob₁₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) →
  Id′ (λ w → A (pop w ₁)) (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂) a₁₀ a₁₁
frob₁₂ A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ =
  coe← (Id′-AP≡ (λ x → (pop x) ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂)
                (AP-AP (pop {B = λ x → A (x ₀)}) _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂))
                A reflʰ reflʰ)
       a₁₂

unfrob₁₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ (λ w → A (pop w ₁)) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) a₁₀ a₁₁) →
  Id′ A (δ ₁₂) a₁₀ a₁₁
unfrob₁₂ A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ =
  coe→ (Id′-AP≡ (λ x → (pop x) ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂)
                (AP-AP (pop {B = λ x → A (x ₀)}) _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂))
                A {a₁₀} {a₁₁} {a₁₀} {a₁₁} reflʰ reflʰ)
       a₁₂

frob₁₂≡ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) →
  frob₁₂ A δ a₀₂ a₁₂ ≡ʰ a₁₂
frob₁₂≡ A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ =
  coe←≡ʰ (Id′-AP≡ (λ x → (pop x) ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂)
                (AP-AP (pop {B = λ x → A (x ₀)}) _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂))
                A reflʰ reflʰ)
       a₁₂

unfrob₁₂≡ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ (λ w → A (pop w ₁)) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) a₁₀ a₁₁) →
  unfrob₁₂ A δ a₀₂ a₁₂ ≡ʰ a₁₂
unfrob₁₂≡ A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ =
  coe→≡ʰ (Id′-AP≡ (λ x → (pop x) ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂)
                (AP-AP (pop {B = λ x → A (x ₀)}) _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂))
                A {a₁₀} {a₁₁} {a₁₀} {a₁₁} reflʰ reflʰ)
       a₁₂

-- This one is a heterogeneous equality because the type of a₁₂ and
-- its (un)frobnications depend on a₀₂ and its (un)frobnications.  And
-- as long as we're being heterogeneous and using UIP, we may as well
-- allow two arbitrary a₀₂'s in the frob and the unfrob.
frob-unfrob₁₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ (λ x → A (x ₀)) δ a₀₀ a₀₁) (a₀₂′ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ (λ w → A (pop w ₁)) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) a₁₀ a₁₁) →
  frob₁₂ A δ a₀₂′ (unfrob₁₂ A δ a₀₂ a₁₂) ≡ʰ a₁₂
frob-unfrob₁₂ A δ {a₀₀} {a₀₁} a₀₂ a₀₂′ {a₁₀} {a₁₁} a₁₂ =
  coe←≡ʰ (Id′-AP≡ (λ x → pop x ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂′)
                  (AP-AP pop _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂′)) A reflʰ reflʰ)
         (coe→ (Id′-AP≡ (λ x → pop x ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂)
               (AP-AP pop _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂)) A reflʰ reflʰ) a₁₂)
  •ʰ coe→≡ʰ (Id′-AP≡ (λ x → pop x ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) (AP-AP pop _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂)) A reflʰ reflʰ) a₁₂

-- This one seems to work homogeneously, and we haven't needed it for
-- anything yet anyway.
unfrob-frob₁₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) →
  unfrob₁₂ A δ (frob₀₂ A δ a₀₂) (frob₁₂ A δ a₀₂ a₁₂) ≡ a₁₂
unfrob-frob₁₂ A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ =
  coe→coe← (Id′-AP≡ (λ x → (pop x) ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂)
                (AP-AP (pop {B = λ x → A (x ₀)}) _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂))
                A reflʰ reflʰ)
