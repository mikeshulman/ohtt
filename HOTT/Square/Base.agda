{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Square.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

------------------------------
-- Square telescopes
------------------------------

-- With the "bundled, collated" definition of identity telescopes, the
-- definition of square telescopes is trivial.
SQ : Tel → Tel
SQ Δ = ID (ID Δ)

-- It's also easy to define the pieces of the boundary of such a square.

infix 40 _₀₀ _₀₁ _₀₂ _₁₀ _₁₁ _₁₂ _₂₀ _₂₁

-- Beta-reducing by hand, we get:

-- ID (Δ ▸ A)      = (δ : ID Δ) ▸ (a₀ : A) ▸ (a₁ ▸ A) ▸ (a₂ : Id′ A δ a₀ a₁)
-- ID (ID (Δ ▸ A))
--  = ID ( (δ : ID Δ) ▸ (a₀ : A)
--                    ▸ (a₁ : A)
--                    ▸ (a₂ : Id′ A δ a₀ a₁) )
--  = (δ : ID (ID A)) ▸ (a₀₀ : A) ▸ (a₀₁ : A) ▸ (a₀₂ : Id′ A ? a₀₀ a₀₁)
--                    ▸ (a₁₀ : A) ▸ (a₁₁ : A) ▸ (a₁₂ : Id′ A ? a₀₀ a₀₁)
--                    ▸ (a₂₀ : Id′ A ? a₀₀ a₁₀) ▸ (a₂₁ : Id′ A ? a₀₁ a₁₁) ▸ (a₁₂ : Id′ (Id′ A) ? a₂₀ a₂₁)

-- Now a first _₀ picks out the first component of each triple produced by the *outermost* ID.  Thus we have

_₀₀ : {Δ : Tel} → el (SQ Δ) → el Δ
δ ₀₀ = δ ₀ ₀

_₁₀ : {Δ : Tel} → el (SQ Δ) → el Δ
δ ₁₀ = δ ₀ ₁                    -- Note reversal!

_₂₀ : {Δ : Tel} → el (SQ Δ) → el (ID Δ)
δ ₂₀ = δ ₀

-- Similarly, a first _₁ picks out the second component of each triple.

_₀₁ : {Δ : Tel} → el (SQ Δ) → el Δ
δ ₀₁ = δ ₁ ₀

_₁₁ : {Δ : Tel} → el (SQ Δ) → el Δ
δ ₁₁ = δ ₁ ₁

_₂₁ : {Δ : Tel} → el (SQ Δ) → el (ID Δ)
δ ₂₁ = δ ₁

-- The other two boundaries δ₀₂ and δ₁₂ seem trickier, but they are
-- actually just AP of _₀ and _₁.

_₀₂ : {Δ : Tel} → el (SQ Δ) → el (ID Δ)
δ ₀₂ = AP _₀ δ

_₁₂ : {Δ : Tel} → el (SQ Δ) → el (ID Δ)
δ ₁₂ = AP _₁ δ

-- Our existing rewrite rules give us the cubical identities definitionally.

₀₂-₀ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₀₂ ₀ ≡ δ ₀₀
₀₂-₀ δ = reflᵉ

₀₂-₁ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₀₂ ₁ ≡ δ ₀₁
₀₂-₁ δ = reflᵉ

₁₂-₀ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₁₂ ₀ ≡ δ ₁₀
₁₂-₀ δ = reflᵉ

₁₂-₁ : {Δ : Tel} (δ : el (SQ Δ)) → δ ₁₂ ₁ ≡ δ ₁₁
₁₂-₁ δ = reflᵉ

-- We can now extract a definition of squares in a type by having Agda
-- normalize (SQ (Δ ▸ A)) for us.  On my laptop this takes:

-- > 15 sec if only the definition of ID is known
-- > 30 sec once AP₀ and AP₁ are declared as rewrites
-- > 1 min once REFL₀ and REFL₁ are also declared as rewrites
-- > 1 min 30 sec once Id′-REFL and AP-const are also declared as rewrites

-- Once done and cleaned up, we obtain:
{-
ID (ID Δ)
▸ (λ x → A (x ₀₀))
▸ (λ x → A ((pop x) ₀₁))
▸ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
▸ (λ x → A ((pop (pop (pop x))) ₁₀))
▸ (λ x → A ((pop (pop (pop (pop x)))) ₁₁))
▸ (λ x → Id′ (λ y → A ((pop y) ₁)) (pop (pop x)) (top (pop x)) (top x))
▸ (λ x → Id′ A (pop (pop (pop (pop (pop (pop x))))) ₀) (top (pop (pop (pop (pop (pop x)))))) (top (pop (pop x))))
▸ (λ x → Id′ A (pop (pop (pop (pop (pop (pop (pop x)))))) ₁) (top (pop (pop (pop (pop (pop x)))))) (top (pop (pop x))))}
▸ (λ x → Id′ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) (pop (pop x)) (top (pop x)) (top x))
-}
-- Here the last term is clearly the type of squares in A.  Rewriting
-- this in terms of its explicit dependencies, we obtain a definition
-- of squares in a type, with boundary slightly frobnified.

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

------------------------------
-- Squares in a type
------------------------------

Sq : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
     {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
     {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
     (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) → Type
Sq {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id′ {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A ((pop x) ₁))}
      (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂) a₂₀ a₂₁

-- We can extend a square in a telescope by a square in a type.
sq∷ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
      {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
      {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
      (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁)
      (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
      el (SQ (Δ ▸ A))
sq∷ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ a₂₂ =
  δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂

-- The "2-simplex" produced by ulift can be regarded as a square.  (TODO: Where does this go?)
{-
ulift→Sq : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀)
  (a₁ a₁' : A δ₁) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') →
  Sq A (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂) (refl a₀) (utr→ A δ₂ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
-}

-- Congruence for squares
Sq≡ : {Δ : Tel} (A : el Δ → Type)
     {δ δ' : el (SQ Δ)} (e : δ ≡ δ')
     {a₀₀ : A (δ ₀₀)} {a₀₀' : A (δ' ₀₀)} (e₀₀ : a₀₀ ≡ʰ a₀₀')
     {a₀₁ : A (δ ₀₁)} {a₀₁' : A (δ' ₀₁)} (e₀₁ : a₀₁ ≡ʰ a₀₁')
     {a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁} {a₀₂' : Id′ A (δ' ₀₂) a₀₀' a₀₁'} (e₀₂ : a₀₂ ≡ʰ a₀₂')
     {a₁₀ : A (δ ₁₀)} {a₁₀' : A (δ' ₁₀)} (e₁₀ : a₁₀ ≡ʰ a₁₀')
     {a₁₁ : A (δ ₁₁)} {a₁₁' : A (δ' ₁₁)} (e₁₁ : a₁₁ ≡ʰ a₁₁')
     {a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁} {a₁₂' : Id′ A (δ' ₁₂) a₁₀' a₁₁'} (e₁₂ : a₁₂ ≡ʰ a₁₂')
     {a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀} {a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀'} (e₂₀ : a₂₀ ≡ʰ a₂₀')
     {a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁} {a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁'} (e₂₁ : a₂₁ ≡ʰ a₂₁') →
  Sq A δ a₀₂ a₁₂ a₂₀ a₂₁ ≡ Sq A δ' a₀₂' a₁₂' a₂₀' a₂₁'
Sq≡ A reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ = reflᵉ
