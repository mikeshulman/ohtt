{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Square.Equality

------------------------------
-- Symmetry
------------------------------

-- Symmetry for telescopes will be defined in terms of symmetry for types.
SYM : (Δ : Tel) → el (SQ Δ) → el (SQ Δ)

-- We also have to define it mutually with proofs that it transposes
-- the boundary.  We expand out the left-hand sides of those that will
-- be rewrites, since rewriting requires the LHS to not be a redex.
postulate
  SYM₀₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₀ ≡ δ ₀₀
  SYM₀₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₀ ≡ δ ₁₀
  SYM₁₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₁ ≡ δ ₀₁
  SYM₁₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₁ ≡ δ ₁₁

{-# REWRITE SYM₀₀ SYM₀₁ SYM₁₀ SYM₁₁ #-}

SYM₀₂ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀₂ ≡ δ ₂₀
SYM₁₂ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁₂ ≡ δ ₂₁
SYM₂₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₂₀ ≡ δ ₀₂
SYM₂₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₂₁ ≡ δ ₁₂

-- Symmetry for types, of course, is a postulated operation, which
-- takes a square over δ to a square over (SYM Δ δ).  It also
-- transposes the boundary, and moreover must coerce the boundary
-- across the above proofs that SYM transposes the boundary.  For
-- reasons explained in Sym.Involution, in the basic postulated
-- operation we also incorporate coercions across equalities of the
-- base square and the boundary (the latter heterogeneous).
postulate
  sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
        {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′₀₂ A δ a₀₀ a₀₁)
        {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′₁₂ A δ a₀₂ a₁₀ a₁₁)
        (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
        {δ' : el (SQ Δ)} (ϕ : δ' ≡ SYM Δ δ)
        {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} (a₀₂' : Id′₀₂ A δ' a₀₀' a₀₁')
        {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} (a₁₂' : Id′₁₂ A δ' a₀₂' a₁₀' a₁₁')
        (a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀') (a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁') →
        (a₀₀' ≡ʰ a₀₀) → (a₀₁' ≡ʰ a₁₀) → (a₀₂' ≡ʰ a₂₀) →
        (a₁₀' ≡ʰ a₀₁) → (a₁₁' ≡ʰ a₁₁) → (a₁₂' ≡ʰ a₂₁) →
        (a₂₀' ≡ʰ a₀₂) → (a₂₁' ≡ʰ a₁₂) →
        Sq A δ a₀₂ a₁₂ a₂₀ a₂₁ →
        Sq A δ' a₀₂' a₁₂' a₂₀' a₂₁'

-- Now we can define symmetry for telescopes by decomposing a collated
-- SQ, transposing and applying symmetry, and recomposing again.
SYM ε δ = []
SYM (Δ ▸ A) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) =
  let a₂₀' = coe← (Id′-AP≡ _₀ (SYM Δ δ) (rev (SYM₀₂ δ)) A reflʰ reflʰ) a₂₀
  in
  SYM Δ δ ∷
  a₀₀ ∷
  a₁₀ ∷
  a₂₀' ∷
  a₀₁ ∷
  a₁₁ ∷
  coe← (Id′-AP≡ (λ x → (pop x ₁)) (SYM Δ δ ∷ a₀₀ ∷ a₁₀ ∷ a₂₀')
                (rev (SYM₁₂ δ) • AP-AP pop _₁ (SYM Δ δ ∷ a₀₀ ∷ a₁₀ ∷ a₂₀')) A reflʰ reflʰ) a₂₁ ∷
  coe→ (Id′-AP≡ _₀ δ (SYM₂₀ δ) A reflʰ reflʰ) a₀₂ ∷
  coe→ (Id′-AP≡ (λ x → (pop x) ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂)
                (SYM₂₁ δ • AP-AP pop _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂)) A reflʰ reflʰ) a₁₂ ∷
  sym A δ a₀₂ a₁₂ a₂₀ a₂₁ reflᵉ _ _ _ _
    reflʰ reflʰ
    (coe←≡ʰ (Id′-AP≡ _₀ (SYM Δ δ) (rev (SYM₀₂ δ)) A reflʰ reflʰ) a₂₀)
    reflʰ reflʰ
    (coe←≡ʰ (Id′-AP≡ (λ x → pop x ₁) (SYM Δ δ ∷ a₀₀ ∷ a₁₀ ∷ a₂₀')
                     (rev (SYM₁₂ δ) • AP-AP pop _₁ (SYM Δ δ ∷ a₀₀ ∷ a₁₀ ∷ a₂₀')) A reflʰ reflʰ) a₂₁)
    (coe→≡ʰ (Id′-AP≡ _₀ δ (SYM₂₀ δ) A reflʰ reflʰ) a₀₂)
    (coe→≡ʰ (Id′-AP≡ (λ x → pop x ₁) (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂) (SYM₂₁ δ • AP-AP pop _₁ (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂)) A reflʰ reflʰ) a₁₂)
    a₂₂

-- It remains to observe that this definition indeed transposes the boundary.

postulate
  SYM₀₂▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ (Δ ▸ A))) → (SYM (Δ ▸ A) δ) ₀₂ ≡ δ ₂₀
  SYM₁₂▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ (Δ ▸ A))) → (SYM (Δ ▸ A) δ) ₁₂ ≡ δ ₂₁
  SYM₂₀▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ (Δ ▸ A))) → (SYM (Δ ▸ A) δ) ₂₀ ≡ δ ₀₂
  SYM₂₁▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ (Δ ▸ A))) → (SYM (Δ ▸ A) δ) ₂₁ ≡ δ ₁₂

SYM₀₂ {ε} δ = reflᵉ
SYM₀₂ {Δ ▸ A} δ = SYM₀₂▸ A δ
-- ID∷≡ A (SYM₀₂ δ) reflʰ reflʰ (coe←≡ʰ (Id′-AP≡ _₀ (SYM Δ δ) (rev (SYM₀₂ δ)) A reflʰ reflʰ) a₂₀)

SYM₁₂ {ε} δ = reflᵉ
SYM₁₂ {Δ ▸ A} δ = SYM₁₂▸ A δ

SYM₂₀ {ε} δ = reflᵉ
SYM₂₀ {Δ ▸ A} δ = SYM₂₀▸ A δ

SYM₂₁ {ε} δ = reflᵉ
SYM₂₁ {Δ ▸ A} δ = SYM₂₁▸ A δ

-- It would be nice to make all the SYMₘₙ equalities into rewrites,
-- but for now we only do this with those for the vertices: SYM₀₀,
-- SYM₀₁, SYM₁₀, and SYM₁₁.  The reason is that these, like AP₀,
-- REFL₀, and so on, are defined recursively purely in terms of
-- themselves, and thus already reduce to reflexivity on concrete
-- telescopes, so making them reduce to reflexivity on abstract
-- telescopes as well is unlikely to be problematic.


-- In contrast, the rules for the 1-cell boundary, SYM₀₂, SYM₁₂,
-- SYM₂₀, and SYM₂₁, involve nontrivial instances of the functoriality
-- rules Id′-AP and AP-AP, and thus don't already reduce to
-- reflexivity even on concrete telescopes -- only on concrete
-- telescopes *of concrete types*.  And unlike Id′-REFL and AP-const,
-- which also have this issue, making them refl as below wouldn't
-- cause their definitions above to also reduce to refl.

{-

{-# REWRITE SYM₀₂ SYM₂₀ SYM₁₂ SYM₂₁ #-}

SYM₀₂-reflᵉ : {Δ : Tel} (δ : el (SQ Δ)) → SYM₀₂ δ ≡ reflᵉ
SYM₀₂-reflᵉ δ = axiomK

SYM₁₂-reflᵉ : {Δ : Tel} (δ : el (SQ Δ)) → SYM₁₂ δ ≡ reflᵉ
SYM₁₂-reflᵉ δ = axiomK

SYM₂₀-reflᵉ : {Δ : Tel} (δ : el (SQ Δ)) → SYM₂₀ δ ≡ reflᵉ
SYM₂₀-reflᵉ δ = axiomK

SYM₂₁-reflᵉ : {Δ : Tel} (δ : el (SQ Δ)) → SYM₂₁ δ ≡ reflᵉ
SYM₂₁-reflᵉ δ = axiomK

{-# REWRITE SYM₀₂-reflᵉ SYM₂₀-reflᵉ SYM₁₂-reflᵉ SYM₂₁-reflᵉ #-}

-}
