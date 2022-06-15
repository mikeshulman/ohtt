{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Square.Top

------------------------------
-- Symmetry
------------------------------

-- Symmetry for telescopes will be defined in terms of symmetry for types.
SYM : (Δ : Tel) → el (SQ Δ) → el (SQ Δ)

-- We also have to define it mutually with proofs that it transposes the boundary.
SYM₀₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₀ ≡ δ ₀₀
SYM₀₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₀ ≡ δ ₁₀
SYM₀₂ : {Δ : Tel} (δ : el (SQ Δ)) → AP _₀ (SYM Δ δ) ≡ δ ₂₀
SYM₁₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ₁ ≡ δ ₀₁
SYM₁₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ₁ ≡ δ ₁₁
SYM₁₂ : {Δ : Tel} (δ : el (SQ Δ)) → AP _₁ (SYM Δ δ) ≡ δ ₂₁
SYM₂₀ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ≡ δ ₀₂
SYM₂₁ : {Δ : Tel} (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ≡ δ ₁₂

-- Symmetry for types, of course, is a postulated operation, which
-- takes a square over δ to a square over (SYM Δ δ).  It also
-- transposes the boundary, and moreover must coerce the boundary
-- across the above proofs that SYM transposes the boundary.  For
-- reasons explained in Sym.Involution, in the basic postulated
-- operation we also incorporate coercions across equalities of the
-- base square and the boundary (the latter heterogeneous).
postulate
  sym′ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
        {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
        {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
        (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
        {δ' : el (SQ Δ)} (ϕ : δ' ≡ SYM Δ δ)
        {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} (a₀₂' : Id′ A (δ' ₀₂) a₀₀' a₀₁')
        {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} (a₁₂' : Id′ A (δ' ₁₂) a₁₀' a₁₁')
        (a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀') (a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁') →
        (a₀₀' ≡ʰ a₀₀) → (a₀₁' ≡ʰ a₁₀) → (a₀₂' ≡ʰ a₂₀) →
        (a₁₀' ≡ʰ a₀₁) → (a₁₁' ≡ʰ a₁₁) → (a₁₂' ≡ʰ a₂₁) →
        (a₂₀' ≡ʰ a₀₂) → (a₂₁' ≡ʰ a₁₂) →
        Sq A δ a₀₂ a₁₂ a₂₀ a₂₁ →
        Sq A δ' a₀₂' a₁₂' a₂₀' a₂₁'

-- From this we can derive the more obvious symmetry operation,
-- without equalities to coerce along.  (Conversely, if we postulated
-- this version, we could derive the coercion version from Sq≡.)
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

-- Now we can define symmetry for telescopes by decomposing a collated
-- SQ, transposing and applying symmetry, and recomposing again.
SYM ε δ = []
SYM (Δ ▸ A) δ =
  sq∷ A (SYM Δ (popsq δ))
    {coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)}
    {coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)}
    (coe← (Id′≡ A (SYM₀₂ (popsq δ)) (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)) (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
          (top₂₀ δ))
    {coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)}
    {coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)}
    (coe← (Id′≡ A (SYM₁₂ (popsq δ)) (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)) (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
          (top₂₁ δ))
    (coe← (Id′≡ A (SYM₂₀ (popsq δ)) (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)) (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)))
          (top₀₂ δ))
    (coe← (Id′≡ A (SYM₂₁ (popsq δ)) (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)) (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
          (top₁₂ δ))
    (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ) (top₂₂ δ))

-- It remains to observe that this definition indeed transposes the boundary.

SYM₀₀ {ε} δ = reflᵉ
SYM₀₀ {Δ ▸ A} δ = ∷≡ A (SYM₀₀ (popsq δ)) (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))

SYM₀₁ {ε} δ = reflᵉ
SYM₀₁ {Δ ▸ A} δ = ∷≡ A (SYM₀₁ (popsq δ)) (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))

SYM₀₂ {ε} δ = reflᵉ
SYM₀₂ {Δ ▸ A} δ =
  ∷≡ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
      -- {AP (λ z → pop (pop (pop z)) ₀) (SYM (Δ ▸ A) δ)
      --   ∷ coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)
      --   ∷ coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)}
      -- {pop (δ ₂₀)}
      (∷≡ (λ y → A (pop y ₁))
           -- {AP (λ z → pop (pop (pop z)) ₀) (SYM (Δ ▸ A) δ)
           --   ∷ coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)}
           -- {pop (pop (δ ₂₀))}
           (∷≡ (λ y → A (y ₀))
                -- {AP (λ z → pop (pop (pop z)) ₀) (SYM (Δ ▸ A) δ)}
                -- {pop (pop (pop (δ ₂₀)))}
                  (rev (AP-AP (λ z → pop (pop (pop z))) _₀ (SYM (Δ ▸ A) δ)) • SYM₀₂ (popsq δ))
                -- {coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)}
                -- {top (pop (pop (δ ₂₀)))}
                (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)))
           -- {coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)}
           -- {top (pop (δ ₂₀))}
           (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
      -- {coe→ (Id′-AP (λ z → pop (pop (pop z)) ₀)
      --               (SYM (Δ ▸ A) δ) A
      --               (coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
      --               (coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
      --   (coe← (Id′-AP (λ x → pop (pop (pop x)))
      --                 (SYM (Δ ▸ A) δ) (λ z → A (z ₀))
      --                 (coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
      --                 (coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
      --     (coe← (Id′-AP _₀ (SYM Δ (popsq δ)) A
      --                   (coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
      --                   (coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
      --       (coe← (Id′≡ A (SYM₀₂ (popsq δ))
      --             (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
      --             (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
      --         (top₂₀ δ))))}
      -- {top (δ ₂₀)}
      (coe→←←←≡ʰ
        (Id′-AP (λ z → pop (pop (pop z)) ₀)
          (SYM (Δ ▸ A) δ) A
          (coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
          (coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
        (Id′-AP (λ x → pop (pop (pop x)))
          (SYM (Δ ▸ A) δ) (λ z → A (z ₀))
          (coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
          (coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
        (Id′-AP _₀ (SYM Δ (popsq δ)) A
          (coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
          (coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
        (Id′≡ A (SYM₀₂ (popsq δ))
          (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
          (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
        (top₂₀ δ))

SYM₁₀ {ε} δ = reflᵉ
SYM₁₀ {Δ ▸ A} δ = ∷≡ A (SYM₁₀ (popsq δ)) (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))

SYM₁₁ {ε} δ = reflᵉ
SYM₁₁ {Δ ▸ A} δ = ∷≡ A (SYM₁₁ (popsq δ)) (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ))

SYM₁₂ {ε} δ = reflᵉ
SYM₁₂ {Δ ▸ A} δ =
  ∷≡ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
    -- {AP (λ z → pop (pop (pop z)) ₁) (SYM (Δ ▸ A) δ)
    --   ∷ coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)
    --   ∷ coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)}
    -- {pop (δ ₂₁)}
    (∷≡ (λ y → A (pop y ₁))
      -- {AP (λ z → pop (pop (pop z)) ₁) (SYM (Δ ▸ A) δ)
      --   ∷ coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)}
      -- {pop (pop (δ ₂₁))}
      (∷≡ (λ y → A (y ₀))
        -- {AP (λ z → pop (pop (pop z)) ₁) (SYM (Δ ▸ A) δ)}
        -- {pop (pop (pop (δ ₂₁)))}
          (rev (AP-AP (λ z → pop (pop (pop z))) _₁ (SYM (Δ ▸ A) δ)) • SYM₁₂ (popsq δ))
        -- {coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)}
        -- {top (pop (pop (δ ₂₁)))}
        (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)))
      -- {coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)}
      -- {top (pop (δ ₂₁))}
      (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
    -- {coe→ (Id′-AP (λ z → pop (pop (pop z)) ₁) (SYM (Δ ▸ A) δ) A
    --         (coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))
    --         (coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
    --  (coe← (Id′-AP (λ x → pop (pop x)) (SYM (Δ ▸ A) δ) (λ z → A (pop z ₁))
    --         (coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))
    --         (coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
    --  (coe← (Id′-AP≡ (λ x → pop x ₁)
    --      (SYM Δ (popsq δ) ∷ coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ) ∷
    --       coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)
    --       ∷
    --       frob₀₂ A (SYM Δ (popsq δ))
    --       (coe←
    --        (Id′≡ A (SYM₀₂ (popsq δ))
    --         (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
    --         (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
    --        (top₂₀ δ)))
    --      (SYM Δ (popsq δ) ₁₂)
    --      (AP-AP pop _₁
    --       (SYM Δ (popsq δ) ∷ coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ) ∷
    --        coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)
    --        ∷
    --        frob₀₂ A (SYM Δ (popsq δ))
    --        (coe←
    --         (Id′≡ A (SYM₀₂ (popsq δ))
    --          (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
    --          (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
    --         (top₂₀ δ))))
    --      A reflʰ reflʰ)
    --  (coe← (Id′≡ A (SYM₁₂ (popsq δ))
    --              (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))
    --              (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
    --        (top₂₁ δ))))}
    -- {top (δ ₂₁)}
    (coe→←←←≡ʰ
      (Id′-AP (λ z → pop (pop (pop z)) ₁) (SYM (Δ ▸ A) δ) A
        (coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))
        (coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
      (Id′-AP (λ x → pop (pop x)) (SYM (Δ ▸ A) δ) (λ z → A (pop z ₁))
        (coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))
        (coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
      (Id′-AP≡ (λ x → pop x ₁)
         (SYM Δ (popsq δ) ∷ coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ) ∷
          coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)
          ∷
          frob₀₂ A (SYM Δ (popsq δ))
          (coe←
           (Id′≡ A (SYM₀₂ (popsq δ))
            (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
            (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
           (top₂₀ δ)))
         (SYM Δ (popsq δ) ₁₂)
         (AP-AP pop _₁
          (SYM Δ (popsq δ) ∷ coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ) ∷
           coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)
           ∷
           frob₀₂ A (SYM Δ (popsq δ))
           (coe←
            (Id′≡ A (SYM₀₂ (popsq δ))
             (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
             (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
            (top₂₀ δ))))
         A reflʰ reflʰ)
      (Id′≡ A (SYM₁₂ (popsq δ))
          (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))
          (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
      (top₂₁ δ))

SYM₂₀ {ε} δ = reflᵉ
SYM₂₀ {Δ ▸ A} δ =
  ∷≡ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
    -- {(SYM Δ (popsq δ) ₀)
    --   ∷ (coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
    --   ∷ (coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ))}
    -- {pop (δ ₀₂)}
    (∷≡ (λ y → A (pop y ₁))
      -- {(SYM Δ (popsq δ) ₀)
      --   ∷ (coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)) }
      -- {pop (pop (δ ₀₂))}
      (∷≡ (λ y → A (y ₀))
        -- {SYM Δ (popsq δ) ₀}
        -- {pop (pop (pop (δ ₀₂)))}
          (SYM₂₀ (popsq δ) • (AP-AP (λ z → pop (pop (pop z))) _₀ δ))
        -- {coe← (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)}
        -- {top (pop (pop (δ ₀₂)))}
        (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ)))
      -- {coe← (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)}
      -- {top (pop (δ ₀₂))}
      (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)))
    -- {coe← (Id′≡ A (SYM₂₀ (popsq δ))
    --                 (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
    --                 (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)))
    --           (top₀₂ δ)}
    -- {top (δ ₀₂)}
    (coe←≡ʰ
      (Id′≡ A (SYM₂₀ (popsq δ))
       (coe←≡ʰ (cong A (SYM₀₀ (popsq δ))) (top₀₀ δ))
       (coe←≡ʰ (cong A (SYM₁₀ (popsq δ))) (top₀₁ δ)))
      (top₀₂ δ)
    •ʰ
    coe→≡ʰcoe→←
    (Id′-AP (_₀ {Δ}) (popsq δ) A (top₀₀ δ) (top₀₁ δ))
    (Id′-AP (λ x → (pop (x ₀))) δ A (top (δ ₀₀)) (top (δ ₀₁)))
    (Id′-AP (λ x → pop (pop (pop x))) δ (λ z → A (z ₀))
            (top (pop (pop (pop (pop (pop (pop (pop (pop δ)))))))))
            (top (pop (pop (pop (pop (pop (pop (pop δ)))))))))
    (top (pop (pop (pop (pop (pop (pop δ))))))))

SYM₂₁ {ε} δ = reflᵉ
SYM₂₁ {Δ ▸ A} δ =
  ∷≡ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
    -- {(SYM Δ (popsq δ) ₁)
    --   ∷ (coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))
    --   ∷ (coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ))}
    -- {pop (δ ₁₂)}
    (∷≡ (λ y → A (pop y ₁))
      -- {(SYM Δ (popsq δ) ₁)
      --   ∷ (coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)) }
      -- {pop (pop (δ ₁₂))}
      (∷≡ (λ y → A (y ₀))
        -- {SYM Δ (popsq δ) ₁}
        -- {pop (pop (pop (δ ₁₂)))}
          (SYM₂₁ (popsq δ) • (AP-AP (λ z → pop (pop (pop z))) _₁ δ))
        -- {coe← (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)}
        -- {top (pop (pop (δ ₁₂)))}
        (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ)))
      -- {coe← (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)}
      -- {top (pop (δ ₁₂))}
      (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
    -- {coe← (Id′≡ A (SYM₂₁ (popsq δ))
    --                 (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))
    --                 (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
    --           (top₁₂ δ)}
    -- {top (δ ₁₂)}
    (coe←≡ʰ
      (Id′≡ A (SYM₂₁ (popsq δ))
       (coe←≡ʰ (cong A (SYM₀₁ (popsq δ))) (top₁₀ δ))
       (coe←≡ʰ (cong A (SYM₁₁ (popsq δ))) (top₁₁ δ)))
      (top₁₂ δ)
    •ʰ
    coe→≡ʰcoe→←
    (Id′-AP≡ (λ x → (pop x) ₁) (popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ top (pop (pop (pop (pop (pop (pop δ))))))) (popsq δ ₁₂)
             (AP-AP (pop {B = λ x → A (x ₀)}) _₁ (popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ top (pop (pop (pop (pop (pop (pop δ))))))))
             A reflʰ reflʰ)
    (Id′-AP (λ x → (pop (pop (pop x)))₁) δ A (top (pop (δ ₀))) (top (pop (δ ₁))))
    (Id′-AP (λ x → pop (pop x)) δ (λ x → A (pop x ₁)) (top (pop (δ ₀))) (top (pop (δ ₁))))
    (top (pop (pop (pop δ)))))

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
