{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
--open import HOTT.Square.Top
--open import HOTT.Square.Equality

------------------------------
-- Symmetry
------------------------------

-- Symmetry for telescopes will be defined in terms of symmetry for types.
SYM : (Δ : Tel) → el (SQ Δ) → el (SQ Δ)

-- We also have to define it mutually with proofs that it transposes the boundary.
SYM₀₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₀ ≡ δ ₀₀
SYM₀₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₀ ≡ δ ₁₀
SYM₁₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₁ ≡ δ ₀₁
SYM₁₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₁ ≡ δ ₁₁
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
  sym′ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
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

-- From this we can derive the more obvious symmetry operation,
-- without equalities to coerce along.  (Conversely, if we postulated
-- this version, we could derive the coercion version from Sq≡.)
{-
sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
        {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
        {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
        (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
        Sq A δ a₀₂ a₁₂ a₂₀ a₂₁ →
        Sq A (SYM Δ δ)
           (coe← (Id′≡ A (SYM₀₂ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)) a₂₀)
           (coe← (Id′≡ A (SYM₁₂ δ) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₂₁)
           (coe← (Id′≡ A (SYM₂₀ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)) a₀₂)
           (coe← (Id′≡ A (SYM₂₁ δ) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₁₂)
sym A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ a₂₂ =
  sym′ A δ a₀₂ a₁₂ a₂₀ a₂₁ reflᵉ
      (coe← (Id′≡ A (SYM₀₂ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)) a₂₀)
      (coe← (Id′≡ A (SYM₁₂ δ) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₂₁)
      (coe← (Id′≡ A (SYM₂₀ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)) a₀₂)
      (coe← (Id′≡ A (SYM₂₁ δ) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₁₂)
      (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀)
      (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)
      (coe←≡ʰ (Id′≡ A (SYM₀₂ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)) a₂₀)
      (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)
      (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)
      (coe←≡ʰ (Id′≡ A (SYM₁₂ δ) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₂₁)
      (coe←≡ʰ (Id′≡ A (SYM₂₀ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)) a₀₂)
      (coe←≡ʰ (Id′≡ A (SYM₂₁ δ) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₁₂)
      a₂₂
-}

-- Now we can define symmetry for telescopes by decomposing a collated
-- SQ, transposing and applying symmetry, and recomposing again.
SYM ε δ = []
SYM (Δ ▸ A) δ =
  let SYMpopδ₀₂ = (SYM Δ (popsq δ) ∷ coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ) ∷ coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ) ∷ coe← (Id′-AP≡ _₀ (SYM Δ (popsq δ)) (rev (SYM₀₂ (popsq δ))) A (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)) (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))) (top₂₀ δ))
  in
  SYM Δ (popsq δ) ∷
  coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ) ∷
  coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ) ∷
  coe← (Id′-AP≡ _₀ (SYM Δ (popsq δ)) (rev (SYM₀₂ (popsq δ))) A (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)) (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))) (top₂₀ δ) ∷
  coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ) ∷
  coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ) ∷
  coe← (Id′-AP≡ (λ x → (pop x ₁)) SYMpopδ₀₂ (rev (SYM₁₂ (popsq δ)) • AP-AP pop _₁ SYMpopδ₀₂) A
                (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)) (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
       (top₂₁ δ) ∷
  coe→ (Id′-AP≡ _₀ (popsq δ) (SYM₂₀ (popsq δ)) A (revʰ (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))) (revʰ (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)))) (top₀₂ δ) ∷
  coe→ (Id′-AP≡ (λ x → (pop x) ₁) (popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ top₀₂ δ) (SYM₂₁ (popsq δ) • AP-AP pop _₁ (popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ top₀₂ δ)) A
                (revʰ (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))) (revʰ (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ))))
       (top₁₂ δ) ∷
  sym′ A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ) reflᵉ _ _ _ _
    (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
    (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))
    (coe←≡ʰ (Id′-AP≡ _₀ (SYM Δ (popsq δ)) (rev (SYM₀₂ (popsq δ))) A (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)) (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))) (top₂₀ δ))
    (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))
    (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ))
    (coe←≡ʰ (Id′-AP≡ (λ x → pop x ₁) SYMpopδ₀₂ (rev (SYM₁₂ (popsq δ)) • AP-AP pop _₁ SYMpopδ₀₂) A
                     (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)) (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
            (top₂₁ δ))
    (coe→≡ʰ (Id′-AP≡ _₀ (popsq δ) (SYM₂₀ (popsq δ)) A (revʰ (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))) (revʰ (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)))) (top₀₂ δ))
    (coe→≡ʰ (Id′-AP≡ (λ x → pop x ₁) (popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ top₀₂ δ) (SYM₂₁ (popsq δ) • AP-AP pop _₁ (popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ top₀₂ δ)) A
                     (revʰ (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))) (revʰ (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ))))
            (top₁₂ δ))
    (top₂₂ δ)

-- It remains to observe that this definition indeed transposes the boundary.

SYM₀₀ {ε} δ = reflᵉ
SYM₀₀ {Δ ▸ A} δ = ∷≡ A (SYM₀₀ (popsq δ)) (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))

SYM₀₁ {ε} δ = reflᵉ
SYM₀₁ {Δ ▸ A} δ = ∷≡ A (SYM₀₁ (popsq δ)) (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))

SYM₁₀ {ε} δ = reflᵉ
SYM₁₀ {Δ ▸ A} δ = ∷≡ A (SYM₁₀ (popsq δ)) (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))

SYM₁₁ {ε} δ = reflᵉ
SYM₁₁ {Δ ▸ A} δ = ∷≡ A (SYM₁₁ (popsq δ)) (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ))

-- The others should be easily provable by combining a few more
-- coercions, but Agda can't manage to normalize their types in a
-- sensible amount of time.  So for now, we just postulate the hard
-- cases.  We also note that we can prove the first few cases by reflᵉ.
postulate
  SYM₀₂▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ (Δ ▸ A))) → (SYM (Δ ▸ A) δ) ₀₂ ≡ δ ₂₀
  SYM₁₂▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ (Δ ▸ A))) → (SYM (Δ ▸ A) δ) ₁₂ ≡ δ ₂₁
  SYM₂₀▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ (Δ ▸ A))) → (SYM (Δ ▸ A) δ) ₂₀ ≡ δ ₀₂
  SYM₂₁▸ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ (Δ ▸ A))) → (SYM (Δ ▸ A) δ) ₂₁ ≡ δ ₁₂

SYM₀₂ {ε} δ = reflᵉ
SYM₀₂ {Δ ▸ A} δ = SYM₀₂▸ A δ

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

{-# REWRITE SYM₀₀ SYM₀₁ SYM₁₀ SYM₁₁ #-}

SYM₀₀-reflᵉ : {Δ : Tel} (δ : el (SQ Δ)) → SYM₀₀ δ ≡ reflᵉ
SYM₀₀-reflᵉ δ = axiomK

SYM₀₁-reflᵉ : {Δ : Tel} (δ : el (SQ Δ)) → SYM₀₁ δ ≡ reflᵉ
SYM₀₁-reflᵉ δ = axiomK

SYM₁₀-reflᵉ : {Δ : Tel} (δ : el (SQ Δ)) → SYM₁₀ δ ≡ reflᵉ
SYM₁₀-reflᵉ δ = axiomK

SYM₁₁-reflᵉ : {Δ : Tel} (δ : el (SQ Δ)) → SYM₁₁ δ ≡ reflᵉ
SYM₁₁-reflᵉ δ = axiomK

{-# REWRITE SYM₀₀-reflᵉ SYM₀₁-reflᵉ SYM₁₀-reflᵉ SYM₁₁-reflᵉ #-}

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
