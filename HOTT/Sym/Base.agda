{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Sym.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Square.Equality

------------------------------
-- Symmetry for telescopes
------------------------------

-- Symmetry for telescopes will be "defined" in terms of symmetry for types.
postulate
  SYM : (Δ : Tel) → el (SQ Δ) → el (SQ Δ)
  -- We also postulate that symmetry on telescopes is an involution.
  -- We should be able to prove this from the analogous fact for
  -- types, but it would be long and annoying, would blow up term size
  -- and slow things down, and we'd want to declare it as a rewrite
  -- anyway.  So we just postulate it.
  SYM-SYM : (Δ : Tel) (δ : el (SQ Δ)) → SYM Δ (SYM Δ δ) ≡ᵉ δ

{-# REWRITE SYM-SYM #-}
  
-- We also have to mutually postulate proofs that SYM transposes the
-- boundary.  We expand out the left-hand sides since rewriting
-- requires the LHS to not be a redex.
postulate
  SYM₀₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₀ ≡ᵉ δ ₀₀
  SYM₀₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₀ ≡ᵉ δ ₁₀
  SYM₁₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₁ ≡ᵉ δ ₀₁
  SYM₁₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₁ ≡ᵉ δ ₁₁
  SYM₀₂ : {Δ : Tel} (δ : el (SQ Δ)) → AP _₀ (SYM Δ δ) ≡ᵉ δ ₂₀
  SYM₁₂ : {Δ : Tel} (δ : el (SQ Δ)) → AP _₁ (SYM Δ δ) ≡ᵉ δ ₂₁
  SYM₂₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ≡ᵉ δ ₀₂
  SYM₂₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ≡ᵉ δ ₁₂

{-# REWRITE SYM₀₀ SYM₀₁ SYM₁₀ SYM₁₁ SYM₀₂ SYM₂₀ SYM₁₂ SYM₂₁ #-}

-- Some more useful variants of Id-AP.
postulate
  Id-AP-₂₀-SYM : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) {a₀₀ : A (δ ₀₀)} {a₁₀ : A (δ ₁₀)} →
    Id A (δ ₂₀) a₀₀ a₁₀ ≡ Id (λ x → A (x ₀)) (SYM Δ δ) a₀₀ a₁₀
  Id-AP-₂₁-SYM : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) {a₀₁ : A (δ ₀₁)} {a₁₁ : A (δ ₁₁)} →
    Id A (δ ₂₁) a₀₁ a₁₁ ≡ Id (λ x → A (x ₁)) (SYM Δ δ) a₀₁ a₁₁

{-# REWRITE Id-AP-₂₀-SYM Id-AP-₂₁-SYM #-}

----------------------------------------
-- Symmetry for types
----------------------------------------

-- Symmetry for types, of course, is a postulated operation, which
-- takes a square over δ to a square over (SYM Δ δ), and transposes
-- the boundary.  However, for reasons explained next to sym-sym
-- below, instead of outputting a square over (SYM Δ δ), it's more
-- convenient to take an exo-equality ϕ : δ' ≡ SYM Δ δ as input, and
-- output a square over δ'.  With this in mind, we wrap up some
-- necessary coercions for the boundaries into lemmas.

sym₀₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) {δ' : el (SQ Δ)} (ϕ : δ' ≡ᵉ SYM Δ δ)
  {a₀₀ : A (δ ₀₀)} {a₁₀ : A (δ ₁₀)} (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) →
  Id₀₂ A δ' (coe← (cong (λ x → A (x ₀₀)) ϕ) a₀₀) (coe← (cong (λ x → A (x ₀₁)) ϕ) a₁₀)
sym₀₂ A δ ϕ {a₀₀} {a₁₀} a₂₀ =
  coe← (Id≡ (λ x → A (x ₀)) ϕ (coe←≡ʰ (cong (λ x → A (x ₀₀)) ϕ) a₀₀) (coe←≡ʰ (cong (λ x → A (x ₀₁)) ϕ) a₁₀)) a₂₀

sym₁₂ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) {δ' : el (SQ Δ)} (ϕ : δ' ≡ᵉ SYM Δ δ)
  {a₀₀ : A (δ ₀₀)} {a₁₀ : A (δ ₁₀)} (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀)
  {a₀₁ : A (δ ₀₁)} {a₁₁ : A (δ ₁₁)} (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
  Id₁₂ A δ' (sym₀₂ A δ ϕ a₂₀) (coe← (cong (λ x → A (x ₁₀)) ϕ) a₀₁) (coe← (cong (λ x → A (x ₁₁)) ϕ) a₁₁)
sym₁₂ {Δ} A δ {δ'} ϕ {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ =
  coe← (rev (Id-AP {ID Δ ▸ (λ x → A (x ₀))} (λ x → pop x)
                    (δ' ∷ coe← (cong (λ x → A (x ₀₀)) ϕ) a₀₀ ∷ coe← (cong (λ x → A (x ₀₁)) ϕ) a₁₀ ∷
                      coe← (Id≡ (λ x → A (x ₀)) ϕ (coe←≡ʰ (cong (λ x → A (x ₀₀)) ϕ) a₀₀) (coe←≡ʰ (cong (λ x → A (x ₀₁)) ϕ) a₁₀)) a₂₀)
                    (λ x → A (x ₁))
                    (coe← (cong (λ x → A (x ₁₀)) ϕ) a₀₁)
                    (coe← (cong (λ x → A (x ₁₁)) ϕ) a₁₁))
            • Id≡ _ ϕ (coe←≡ʰ (cong (λ x → A (x ₁₀)) ϕ) a₀₁) (coe←≡ʰ (cong (λ x → A (x ₁₁)) ϕ) a₁₁))
        a₂₁

sym₂₀ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) {δ' : el (SQ Δ)} (ϕ : δ' ≡ᵉ SYM Δ δ)
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁) →
  Id (λ x → A (x ₀)) (SYM Δ δ') (coe← (cong (λ x → A (x ₀₀)) ϕ) a₀₀) (coe← (cong (λ x → A (x ₁₀)) ϕ) a₀₁)
sym₂₀ {Δ} A δ ϕ {a₀₀} {a₀₁} a₀₂ = coe← (Id≡ _ (congᵉ (SYM Δ) ϕ) (coe←≡ʰ (cong (λ x → A (x ₀₀)) ϕ) a₀₀) (coe←≡ʰ (cong (λ x → A (x ₁₀)) ϕ) a₀₁)) a₀₂

sym₂₁ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ)) {δ' : el (SQ Δ)} (ϕ : δ' ≡ᵉ SYM Δ δ)
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id₁₂ A δ a₀₂ a₁₀ a₁₁) →
  Id (λ x → A (x ₁)) (SYM Δ δ') (coe← (cong (λ x → A (x ₀₁)) ϕ) a₁₀) (coe← (cong (λ x → A (x ₁₁)) ϕ) a₁₁)
sym₂₁ {Δ} A δ ϕ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ =
  coe← (Id≡ _ (congᵉ (SYM Δ) ϕ) (coe←≡ʰ (cong (λ x → A (x ₀₁)) ϕ) a₁₀) (coe←≡ʰ (cong (λ x → A (x ₁₁)) ϕ) a₁₁) •
       Id-AP pop (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) (λ x → A (x ₁)) a₁₀ a₁₁) a₁₂

-- Now we can postulate this generalized version of symmetry, which we
-- call sym′.
postulate
  sym′ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id₁₂ A δ a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
    {δ' : el (SQ Δ)} (ϕ : δ' ≡ᵉ SYM Δ δ)
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
    Sq A δ'
      {coe← (cong (λ x → A (x ₀₀)) ϕ) a₀₀}
      {coe← (cong (λ x → A (x ₀₁)) ϕ) a₁₀}
      (sym₀₂ A δ ϕ a₂₀)
      {coe← (cong (λ x → A (x ₁₀)) ϕ) a₀₁}
      {coe← (cong (λ x → A (x ₁₁)) ϕ) a₁₁}
      (sym₁₂ A δ ϕ a₂₀ a₂₁)
      (sym₂₀ A δ ϕ a₀₂)
      (sym₂₁ A δ ϕ a₀₂ a₁₂)

-- The simpler version of symmetry is defined from this.
sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id₁₂ A δ a₀₂ a₁₀ a₁₁)
  (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁)
  (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
  Sq A (SYM Δ δ)
    {a₀₀} {a₁₀} a₂₀
    {a₀₁} {a₁₁} (Id-pop→ (λ x → A (x ₁)) (λ w → A (w ₀)) (SYM Δ δ) a₂₀ a₂₁)
    a₀₂ (Id-pop← (λ x → A (x ₁)) (λ w → A (w ₀)) δ a₀₂ a₁₂)
sym {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ a₂₂ =
  sym′ A δ a₀₂ a₁₂ a₂₀ a₂₁ reflᵉᵉ a₂₂

-- Now we can "define" symmetry for telescopes by decomposing a collated
-- SQ, transposing and applying symmetry, and recomposing again.
postulate
  SYMε : (δ : el (SQ ε)) → SYM ε δ ≡ᵉ []
  SYM▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id₁₂ A δ a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
      SYM (Δ ▸ A) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) ≡ᵉ
        SYM Δ δ
        ∷ a₀₀ ∷ a₁₀ ∷ a₂₀
        ∷ a₀₁ ∷ a₁₁ ∷ (Id-pop→ (λ x → A (x ₁)) (λ w → A (w ₀)) (SYM Δ δ) a₂₀ a₂₁)
        ∷ a₀₂ ∷ (Id-pop← (λ x → A (x ₁)) (λ w → A (w ₀)) δ a₀₂ a₁₂)
        ∷ sym A δ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂

{-# REWRITE SYMε SYM▸ #-}

----------------------------------------
-- Symmetry is an involution
----------------------------------------

-- We would like to declare the fact that symmetry on types is an
-- involution as a rewrite.  Unfortunately, the naive postulate that
-- would look something like
---
--- sym-sym : ... → sym A (SYM Δ δ) ... (sym A δ ... a₂₂) ≡ a₂₂
---
-- isn't very suitable as a rewrite, because it has the volatile SYM
-- on the left.  When Δ is concrete, this SYM will reduce, and Agda
-- won't be able to un-reduce it to notice that the two sym's match.
-- This is the main reason for postulating instead the enhanced
-- symmetry sym′, that incorporates coercion across equalities.  It
-- allows us to formulate the version of sym-sym,below, whose LHS is
-- not volatile and can hopefully be pattern-matched so that the
-- rewrite will fire.  In practice, I expect that ϕ will always be
-- refl, so that all the nasty coercions will reduce away.

postulate
  sym-sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id₀₂ A δ a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id₁₂ A δ a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁)
    {δ' : el (SQ Δ)} (ϕ : δ' ≡ᵉ SYM Δ δ)
    {δ'' : el (SQ Δ)} (ϕ' : δ'' ≡ᵉ SYM Δ δ')
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
    sym′ A δ' (sym₀₂ A δ ϕ a₂₀) (sym₁₂ A δ ϕ a₂₀ a₂₁) (sym₂₀ A δ ϕ a₀₂) (sym₂₁ A δ ϕ a₀₂ a₁₂) ϕ' (sym′ A δ a₀₂ a₁₂ a₂₀ a₂₁ ϕ a₂₂) ≡
      coe← (Sq≡ A (ϕ' •ᵉ (congᵉ (SYM Δ) ϕ))
             -- Do I seriously have to write out all these arguments?
             -- Can't Agda notice these things are double coercions?
             (coe←←≡ʰ (cong (λ x → A (x ₀₀)) ϕ') (cong (λ x → A (x ₀₀)) ϕ) a₀₀)
             (coe←←≡ʰ (cong (λ x → A (x ₀₁)) ϕ') (cong (λ x → A (x ₁₀)) ϕ) a₀₁)
             (coe←←≡ʰ (Id≡ (λ x → A (x ₀)) ϕ' (coe←≡ʰ (cong (λ x → A (x ₀₀)) ϕ') _) (coe←≡ʰ (cong (λ x → A (x ₀₁)) ϕ') _))
                      (Id≡ _ (congᵉ (SYM Δ) ϕ) (coe←≡ʰ (cong (λ x → A (x ₀₀)) ϕ) a₀₀) (coe←≡ʰ (cong (λ x → A (x ₁₀)) ϕ) a₀₁))
                      a₀₂)
             (coe←←≡ʰ (cong (λ x → A (x ₁₀)) ϕ') (cong (λ x → A (x ₀₁)) ϕ) a₁₀)
             (coe←←≡ʰ (cong (λ x → A (x ₁₁)) ϕ') (cong (λ x → A (x ₁₁)) ϕ) a₁₁)
             (coe←←≡ʰ (rev (Id-AP {ID Δ ▸ (λ x → A (x ₀))} (λ x → pop x)
                    (δ'' ∷ coe← (cong (λ x → A (x ₀₀)) ϕ') _ ∷ coe← (cong (λ x → A (x ₀₁)) ϕ') _ ∷
                      coe← (Id≡ (λ x → A (x ₀)) ϕ' (coe←≡ʰ (cong (λ x → A (x ₀₀)) ϕ') _) (coe←≡ʰ (cong (λ x → A (x ₀₁)) ϕ') _)) _)
                    (λ x → A (x ₁))
                    (coe← (cong (λ x → A (x ₁₀)) ϕ') _)
                    (coe← (cong (λ x → A (x ₁₁)) ϕ') _))
                      • Id≡ _ ϕ' (coe←≡ʰ (cong (λ x → A (x ₁₀)) ϕ') _) (coe←≡ʰ (cong (λ x → A (x ₁₁)) ϕ') _))
                    (Id≡ _ (congᵉ (SYM Δ) ϕ) (coe←≡ʰ (cong (λ x → A (x ₀₁)) ϕ) a₁₀) (coe←≡ʰ (cong (λ x → A (x ₁₁)) ϕ) a₁₁) •
                    Id-AP pop (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) (λ x → A (x ₁)) a₁₀ a₁₁)
                    a₁₂)
             (coe←←≡ʰ (Id≡ _ (congᵉ (SYM Δ) ϕ') (coe←≡ʰ (cong (λ x → A (x ₀₀)) ϕ') _) (coe←≡ʰ (cong (λ x → A (x ₁₀)) ϕ') _))
                      (Id≡ (λ x → A (x ₀)) ϕ (coe←≡ʰ (cong (λ x → A (x ₀₀)) ϕ) a₀₀) (coe←≡ʰ (cong (λ x → A (x ₀₁)) ϕ) a₁₀))
                      a₂₀)
             (coe←←≡ʰ (Id≡ _ (congᵉ (SYM Δ) ϕ') (coe←≡ʰ (cong (λ x → A (x ₀₁)) ϕ') _) (coe←≡ʰ (cong (λ x → A (x ₁₁)) ϕ') _) •
                    Id-AP pop (δ' ∷ coe← (cong (λ x → A (x ₀₀)) ϕ) a₀₀ ∷ coe← (cong (λ x → A (x ₀₁)) ϕ) a₁₀ ∷ sym₀₂ A δ ϕ a₂₀) (λ x → A (x ₁)) _ _)
                    (rev (Id-AP {ID Δ ▸ (λ x → A (x ₀))} (λ x → pop x)
                    (δ' ∷ coe← (cong (λ x → A (x ₀₀)) ϕ) a₀₀ ∷ coe← (cong (λ x → A (x ₀₁)) ϕ) a₁₀ ∷
                      coe← (Id≡ (λ x → A (x ₀)) ϕ (coe←≡ʰ (cong (λ x → A (x ₀₀)) ϕ) a₀₀) (coe←≡ʰ (cong (λ x → A (x ₀₁)) ϕ) a₁₀)) a₂₀)
                    (λ x → A (x ₁))
                    (coe← (cong (λ x → A (x ₁₀)) ϕ) a₀₁)
                    (coe← (cong (λ x → A (x ₁₁)) ϕ) a₁₁))
                    • Id≡ _ ϕ (coe←≡ʰ (cong (λ x → A (x ₁₀)) ϕ) a₀₁) (coe←≡ʰ (cong (λ x → A (x ₁₁)) ϕ) a₁₁))
                    a₂₁))
           a₂₂

{-# REWRITE sym-sym #-}
