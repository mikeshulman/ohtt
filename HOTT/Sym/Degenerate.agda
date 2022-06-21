{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Square.Equality
open import HOTT.Square.Boundary
open import HOTT.Sym.Base
open import HOTT.Sym.Naturality

postulate
  AP-REFL′ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) →
    AP (λ x → REFL (f x)) γ ≡ SYM Δ (REFL (AP f γ))

postulate
  ap-refl : {Δ : Tel} (A : el Δ → Type) (f : (x : el Δ) → A x) (δ : el (ID Δ)) →
    ap (λ x → refl (f x)) δ ≡
    coe← (Id′-AP {Δ} {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))} (λ x → REFL x ∷ f x ∷ f x)
                 δ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y)) (refl (f (δ ₀))) (refl (f (δ ₁))))
         ((sym A (REFL δ)
             {f (δ ₀)} {f (δ ₀)} (frob₀₂ A (REFL δ) (refl (f (δ ₀))))
             {f (δ ₁)} {f (δ ₁)} (frob₁₂ A (REFL δ) (refl (f (δ ₀))) (refl (f (δ ₁))))
             (ap f δ) (ap f δ)
             (AP-REFL′ {Δ} {Δ} (λ x → x) δ)
             {f (δ ₀)} {f (δ ₁)} (coe→ (Id′-AP REFL δ (λ z → A (z ₀)) (f (δ ₀)) (f (δ ₁))) (ap f δ))
             {f (δ ₀)} {f (δ ₁)} (coe→ (Id′-AP (λ z → REFL z ∷ f z) δ (λ z → A (pop z ₁)) (f (δ ₀)) (f (δ ₁))) (ap f δ))
             (refl (f (δ ₀))) (refl (f (δ ₁)))
             reflʰ reflʰ (coe→≡ʰ (Id′-AP REFL δ (λ z → A (z ₀)) (f (δ ₀)) (f (δ ₁))) (ap f δ))
             reflʰ reflʰ (coe→≡ʰ (Id′-AP (λ z → REFL z ∷ f z) δ (λ z → A (pop z ₁)) (f (δ ₀)) (f (δ ₁))) (ap f δ))
             (revʰ (frob₀₂≡ A (REFL δ) (refl (f (δ ₀)))))
             (revʰ (frob₁₂≡ A (REFL δ) (refl (f (δ ₀))) (refl (f (δ ₁)))))
             (coe→ (Id′-AP≡ {ε} {ID Δ ▸ (λ x → A (x ₀)) ▸ (λ x → A (pop x ₁))} (λ _ → δ ∷ f (δ ₀) ∷ f (δ ₁)) []
                      (sq₁₂≡ A {REFL δ} {REFL δ} reflᵉ reflʰ reflʰ
                         (coe←≡ʰ (Id′-AP _₀ (REFL δ) A (f (δ ₀)) (f (δ ₀))) (refl (f (δ ₀)))) reflʰ reflʰ
                         (coe←≡ʰ (Id′-AP≡ (λ x → pop x ₁)
                                   (REFL δ ∷ f (δ ₀) ∷ f (δ ₀) ∷
                                     coe← (Id′-AP _₀ (REFL δ) A (f (δ ₀)) (f (δ ₀))) (refl (f (δ ₀))))
                                   (AP-AP pop _₁
                                     (REFL δ ∷ f (δ ₀) ∷ f (δ ₀) ∷ coe← (Id′-AP _₀ (REFL δ) A (f (δ ₀)) (f (δ ₀))) (refl (f (δ ₀)))))
                                   A reflʰ reflʰ)
                                 (refl (f (δ ₁)))
                         •ʰ revʰ (coe→≡ʰ (Id′-AP (λ _ → _∷_ {ID Δ} {λ x → A (x ₀)} δ (f (δ ₀))) [] (λ z → A (pop z ₁)) (f (δ ₁)) (f (δ ₁)))
                                          (ap (λ _ → f (δ ₁)) []))))
                      (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
                      {ap f δ} {ap f δ} reflʰ {ap f δ} {ap f δ} reflʰ)
                    (refl (ap f δ)))))

{-# REWRITE ap-refl #-}

postulate
  AP-REFL′-ε : {Γ : Tel} (f : el Γ → el ε) (γ : el (ID Γ)) →
    AP-REFL′ {Γ} {ε} f γ ≡ reflᵉ
  AP-REFL′-∷ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el Δ) (g : (x : el Γ) → A (f x)) (γ : el (ID Γ)) →
    AP-REFL′ {Γ} {Δ ▸ A} (λ x → f x ∷ g x) γ ≡
    (sq₂₂≡ A (AP-REFL′ f γ) reflʰ reflʰ
      (coe→≡ʰ (Id′-AP (λ z → REFL (f z)) γ (λ z → A (z ₀)) (g (γ ₀)) (g (γ ₁))) (ap g γ)
       •ʰ revʰ (coe←≡ʰ (Id′-AP≡ _₀ (SYM Δ (REFL (AP (λ z → f z) γ))) (rev (SYM₀₂ (REFL (AP (λ z → f z) γ)))) A reflʰ reflʰ)
                      (coe→ (Id′-AP (λ z → f z) γ (λ z → A z) (g (γ ₀)) (g (γ ₁))) (ap g γ))
              •ʰ coe→≡ʰ (Id′-AP (λ z → f z) γ (λ z → A z) (g (γ ₀)) (g (γ ₁))) (ap g γ)))
      reflʰ reflʰ
      (coe→≡ʰ (Id′-AP (λ z → REFL (f z) ∷ g z) γ (λ z → A (pop z ₁)) (g (γ ₀)) (g (γ ₁))) (ap (λ z → g z) γ)
      •ʰ revʰ (coe←≡ʰ
      (Id′-AP≡ (λ x → pop x ₁)
       (SYM Δ (REFL (AP (λ z → f z) γ)) ∷ g (γ ₀) ∷ g (γ ₁) ∷
        coe←
        (Id′-AP≡ _₀ (SYM Δ (REFL (AP (λ z → f z) γ)))
         (rev (SYM₀₂ (REFL (AP (λ z → f z) γ)))) A reflʰ reflʰ)
        (coe→ (Id′-AP (λ z → f z) γ (λ z → A z) (g (γ ₀)) (g (γ ₁)))
         (ap (λ z → g z) γ)))
       (rev (SYM₁₂ (REFL (AP (λ z → f z) γ))) •
        AP-AP pop _₁
        (SYM Δ (REFL (AP (λ z → f z) γ)) ∷ g (γ ₀) ∷ g (γ ₁) ∷
         coe←
         (Id′-AP≡ _₀ (SYM Δ (REFL (AP (λ z → f z) γ)))
          (rev (SYM₀₂ (REFL (AP (λ z → f z) γ)))) A reflʰ reflʰ)
         (coe→ (Id′-AP (λ z → f z) γ (λ z → A z) (g (γ ₀)) (g (γ ₁)))
          (ap (λ z → g z) γ))))
       A reflʰ reflʰ)
      (coe→ (Id′-AP (λ z → f z) γ (λ z → A z) (g (γ ₀)) (g (γ ₁)))
       (ap (λ z → g z) γ))
       •ʰ coe→≡ʰ (Id′-AP (λ z → f z) γ (λ z → A z) (g (γ ₀)) (g (γ ₁))) (ap (λ z → g z) γ)))
      (revʰ (coe→≡ʰ (Id′-AP≡ _₀ (REFL (AP (λ z → f z) γ)) (SYM₂₀ (REFL (AP (λ z → f z) γ))) A reflʰ reflʰ) (refl (g (γ ₀)))))
      (revʰ (coe→≡ʰ (Id′-AP≡ (λ x → pop x ₁)
        (REFL (_∷_ {ID Δ} {λ x → A (x ₀)} (AP f γ) (g (γ ₀))))
        (SYM₂₁ (REFL (AP f γ)) •
          AP-AP pop _₁ (REFL (AP f γ) ∷ g (γ ₀) ∷ g (γ ₀) ∷ refl (g (γ ₀))))
        A {g (γ ₁)} {g (γ ₁)} reflʰ {g (γ ₁)} {g (γ ₁)} reflʰ)
        (refl (g (γ ₁)))))
      ( coe→≡ʰ
      (Id′-AP (λ z → REFL (f z) ∷ g z ∷ g z) γ
       (λ z → Id′ A (pop (pop z)) (top (pop z)) (top z)) (refl (g (γ ₀)))
       (refl (g (γ ₁))))
      (coe←
       (Id′-AP (λ x → REFL x ∷ g x ∷ g x) γ
        (λ y → Id′ (λ z → A (f z)) (pop (pop y)) (top (pop y)) (top y))
        (refl (g (γ ₀))) (refl (g (γ ₁))))
       (sym (λ z → A (f z)) (REFL γ)
        (frob₀₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀))))
        (frob₁₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀))) (refl (g (γ ₁))))
        (ap (λ z → g z) γ) (ap (λ z → g z) γ) (AP-REFL′ (λ x → x) γ)
        (coe→ (Id′-AP REFL γ (λ z → A (f (z ₀))) (g (γ ₀)) (g (γ ₁)))
         (ap (λ z → g z) γ))
        (coe→
         (Id′-AP (λ z → REFL z ∷ g z) γ (λ z → A (f (pop z ₁))) (g (γ ₀))
          (g (γ ₁)))
         (ap (λ z → g z) γ))
        (refl (g (γ ₀))) (refl (g (γ ₁))) reflʰ reflʰ
        (coe→≡ʰ (Id′-AP REFL γ (λ z → A (f (z ₀))) (g (γ ₀)) (g (γ ₁)))
         (ap (λ z → g z) γ))
        reflʰ reflʰ
        (coe→≡ʰ
         (Id′-AP (λ z → REFL z ∷ g z) γ (λ z → A (f (pop z ₁))) (g (γ ₀))
          (g (γ ₁)))
         (ap (λ z → g z) γ))
        (revʰ (frob₀₂≡ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀)))))
        (revʰ
         (frob₁₂≡ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀)))
          (refl (g (γ ₁)))))
        (coe→
         (Id′-AP≡ (λ _ → γ ∷ g (γ ₀) ∷ g (γ ₁)) []
          (sq₁₂≡ (λ z → A (f z)) reflᵉ reflʰ reflʰ
           (coe←≡ʰ (Id′-AP _₀ (REFL γ) (λ z → A (f z)) (g (γ ₀)) (g (γ ₀)))
            (refl (g (γ ₀))))
           reflʰ reflʰ
           (coe←≡ʰ
            (Id′-AP≡ (λ x → pop x ₁)
             (REFL γ ∷ g (γ ₀) ∷ g (γ ₀) ∷
              frob₀₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀))))
             (AP-AP pop _₁
              (REFL γ ∷ g (γ ₀) ∷ g (γ ₀) ∷
               frob₀₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀)))))
             (λ z → A (f z)) reflʰ reflʰ)
            (refl (g (γ ₁)))
            •ʰ reflʰ))
          (λ y → Id′ (λ z → A (f z)) (pop (pop y)) (top (pop y)) (top y))
          reflʰ reflʰ)
         (refl (ap (λ z → g z) γ)))))
        •ʰ
       (coe←≡ʰ
       (Id′-AP (λ x → REFL x ∷ g x ∷ g x) γ
        (λ y → Id′ (λ z → A (f z)) (pop (pop y)) (top (pop y)) (top y))
        (refl (g (γ ₀))) (refl (g (γ ₁))))
       (sym (λ z → A (f z)) (REFL γ)
        (frob₀₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀))))
        (frob₁₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀))) (refl (g (γ ₁))))
        (ap (λ z → g z) γ) (ap (λ z → g z) γ) (AP-REFL′ (λ x → x) γ)
        (coe→ (Id′-AP REFL γ (λ z → A (f (z ₀))) (g (γ ₀)) (g (γ ₁)))
         (ap (λ z → g z) γ))
        (coe→
         (Id′-AP (λ z → REFL z ∷ g z) γ (λ z → A (f (pop z ₁))) (g (γ ₀))
          (g (γ ₁)))
         (ap (λ z → g z) γ))
        (refl (g (γ ₀))) (refl (g (γ ₁))) reflʰ reflʰ
        (coe→≡ʰ (Id′-AP REFL γ (λ z → A (f (z ₀))) (g (γ ₀)) (g (γ ₁)))
         (ap (λ z → g z) γ))
        reflʰ reflʰ
        (coe→≡ʰ
         (Id′-AP (λ z → REFL z ∷ g z) γ (λ z → A (f (pop z ₁))) (g (γ ₀))
          (g (γ ₁)))
         (ap (λ z → g z) γ))
        (revʰ (frob₀₂≡ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀)))))
        (revʰ
         (frob₁₂≡ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀)))
          (refl (g (γ ₁)))))
        (coe→
         (Id′-AP≡ (λ _ → γ ∷ g (γ ₀) ∷ g (γ ₁)) []
          (sq₁₂≡ (λ z → A (f z)) reflᵉ reflʰ reflʰ
           (coe←≡ʰ (Id′-AP _₀ (REFL γ) (λ z → A (f z)) (g (γ ₀)) (g (γ ₀)))
            (refl (g (γ ₀))))
           reflʰ reflʰ
           (coe←≡ʰ
            (Id′-AP≡ (λ x → pop x ₁)
             (REFL γ ∷ g (γ ₀) ∷ g (γ ₀) ∷
              frob₀₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀))))
             (AP-AP pop _₁
              (REFL γ ∷ g (γ ₀) ∷ g (γ ₀) ∷
               frob₀₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀)))))
             (λ z → A (f z)) reflʰ reflʰ)
            (refl (g (γ ₁)))
            •ʰ reflʰ))
          (λ y → Id′ (λ z → A (f z)) (pop (pop y)) (top (pop y)) (top y))
          reflʰ reflʰ)
         (refl (ap (λ z → g z) γ)))))
          •ʰ {!sym-AP f A (REFL γ) (frob₀₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀))))
    (frob₁₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀))) (refl (g (γ ₁))))
    (ap (λ z → g z) γ) (ap (λ z → g z) γ) (AP-REFL′ (λ x → x) γ)
    (coe→ (Id′-AP REFL γ (λ z → A (f (z ₀))) (g (γ ₀)) (g (γ ₁)))
     (ap (λ z → g z) γ))
    (coe→
     (Id′-AP (λ z → REFL z ∷ g z) γ (λ z → A (f (pop z ₁))) (g (γ ₀))
      (g (γ ₁)))
     (ap (λ z → g z) γ))
    (refl (g (γ ₀))) (refl (g (γ ₁))) reflʰ reflʰ
    (coe→≡ʰ (Id′-AP REFL γ (λ z → A (f (z ₀))) (g (γ ₀)) (g (γ ₁)))
     (ap (λ z → g z) γ))
    reflʰ reflʰ
    (coe→≡ʰ
     (Id′-AP (λ z → REFL z ∷ g z) γ (λ z → A (f (pop z ₁))) (g (γ ₀))
      (g (γ ₁)))
     (ap (λ z → g z) γ))
    (revʰ (frob₀₂≡ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀)))))
    (revʰ
     (frob₁₂≡ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀)))
      (refl (g (γ ₁)))))
    (coe→
     (Id′-AP≡ (λ _ → γ ∷ g (γ ₀) ∷ g (γ ₁)) []
      (sq₁₂≡ (λ z → A (f z)) reflᵉ reflʰ reflʰ
       (coe←≡ʰ (Id′-AP _₀ (REFL γ) (λ z → A (f z)) (g (γ ₀)) (g (γ ₀)))
        (refl (g (γ ₀))))
       reflʰ reflʰ
       (coe←≡ʰ
        (Id′-AP≡ (λ x → pop x ₁)
         (REFL γ ∷ g (γ ₀) ∷ g (γ ₀) ∷
          frob₀₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀))))
         (AP-AP pop _₁
          (REFL γ ∷ g (γ ₀) ∷ g (γ ₀) ∷
           frob₀₂ (λ z → A (f z)) (REFL γ) (refl (g (γ ₀)))))
         (λ z → A (f z)) reflʰ reflʰ)
        (refl (g (γ ₁)))
        •ʰ reflʰ))
      (λ y → Id′ (λ z → A (f z)) (pop (pop y)) (top (pop y)) (top y))
      reflʰ reflʰ)
     (refl (ap (λ z → g z) γ)))
     -- start arguments of second sym
     
     !}))

--{-# REWRITE AP-REFL′-ε AP-REFL′-∷ #-}
