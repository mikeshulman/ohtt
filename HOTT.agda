{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT where

open import Agda.Primitive renaming (Set to Type; SSet to Typeᵉ) public

data _≡_ {A : Typeᵉ} (a : A) : A → Typeᵉ where
  reflᵉ : a ≡ a

_•_ : {A : Type} {a b c : A} (p : a ≡ b) (q : b ≡ c) → a ≡ c
reflᵉ • reflᵉ = reflᵉ

rev : {A : Type} {a b : A} (p : a ≡ b) → b ≡ a
rev reflᵉ = reflᵉ

cong : {A B : Type} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
cong f reflᵉ = reflᵉ

coe→ : {A : Type} (B : A → Type) {x y : A} (p : x ≡ y) (u : B x) → B y
coe→ B reflᵉ u = u

coe← : {A : Type} (B : A → Type) {x y : A} (p : x ≡ y) (v : B y) → B x
coe← B reflᵉ v = v

axk : {A : Type} {a : A} (p : a ≡ a) → p ≡ reflᵉ
axk reflᵉ = reflᵉ

uip : {A : Type} {a b : A} (p q : a ≡ b) → p ≡ q
uip p reflᵉ = axk p

{-# BUILTIN REWRITE _≡_ #-}

-- Identity types

postulate
  Id : (A : Type) → A → A → Type
  refl : {A : Type} (a : A) → Id A a a
  Id¹ : {Δ : Type} (A : Δ → Type) {δ δ' : Δ} (ρ : Id Δ δ δ') → A δ → A δ' → Type
  ap : {Δ : Type} {A : Δ → Type} (f : (u : Δ) → A u) {δ δ' : Δ} (ρ : Id Δ δ δ') → Id¹ A ρ (f δ) (f δ')
  Id² : {Δ₀ : Type} {Δ₁ : Δ₀ → Type} (A : (x : Δ₀) → Δ₁ x → Type)
        {δ₀ δ₀' : Δ₀} (ρ₀ : Id Δ₀ δ₀ δ₀') {δ₁ : Δ₁ δ₀} {δ₁' : Δ₁ δ₀'} (ρ₁ : Id¹ Δ₁ ρ₀ δ₁ δ₁') →
        A δ₀ δ₁ → A δ₀' δ₁' → Type
  ap² : {Δ₀ : Type} {Δ₁ : Δ₀ → Type} {A : (x : Δ₀) → Δ₁ x → Type} (f : (x : Δ₀) (y : Δ₁ x) → A x y)
        {δ₀ δ₀' : Δ₀} (ρ₀ : Id Δ₀ δ₀ δ₀') {δ₁ : Δ₁ δ₀} {δ₁' : Δ₁ δ₀'} (ρ₁ : Id¹ Δ₁ ρ₀ δ₁ δ₁') →
        Id² A ρ₀ ρ₁ (f δ₀ δ₁) (f δ₀' δ₁')

postulate
  Id¹-const : {Δ : Type} (A : Type) {δ δ' : Δ} (ρ : Id Δ δ δ') (a₀ a₁ : A) → Id¹ (λ _ → A) ρ a₀ a₁ ≡ Id A a₀ a₁
  Id¹-refl : {Δ : Type} (A : Δ → Type) (δ : Δ) (a₀ a₁ : A δ) → Id¹ A (refl δ) a₀ a₁ ≡ Id (A δ) a₀ a₁

{-# REWRITE Id¹-const Id¹-refl #-}

postulate
  Id²-const : {Δ₀ : Type} {Δ₁ : Δ₀ → Type} (A : Δ₀ → Type)
              {δ₀ δ₀' : Δ₀} (ρ₀ : Id Δ₀ δ₀ δ₀') {δ₁ : Δ₁ δ₀} {δ₁' : Δ₁ δ₀'} (ρ₁ : Id¹ Δ₁ ρ₀ δ₁ δ₁') →
              (a : A δ₀) (a' : A δ₀') → Id² {Δ₁ = Δ₁} (λ x y → A x) ρ₀ ρ₁ a a' ≡ Id¹ A ρ₀ a a'
  Id²-refl : {Δ₀ : Type} {Δ₁ : Δ₀ → Type} (A : (x : Δ₀) → Δ₁ x → Type)
             {δ₀ : Δ₀} {δ₁ δ₁' : Δ₁ δ₀} (ρ₁ : Id (Δ₁ δ₀) δ₁ δ₁') (a : A δ₀ δ₁) (a' : A δ₀ δ₁') →
             Id² A (refl δ₀) ρ₁ a a' ≡ Id¹ (A δ₀) ρ₁ a a'

{-# REWRITE Id²-const Id²-refl #-}

postulate
  ap-const : {Δ : Type} (A : Type) (f : A) {δ δ' : Δ} (ρ : Id Δ δ δ') → ap (λ _ → f) ρ ≡ refl f
  ap-refl : {Δ : Type} {A : Δ → Type} (f : (u : Δ) → A u) (δ : Δ) → ap f (refl δ) ≡ refl (f δ)
  ap-idmap : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') → ap (λ x → x) ρ ≡ ρ
  -- This should really compute in the other direction.  (In actual HOTT, it is proven admissible over the structure of A.)  But Agda can't compute it in that direction.  In this direction, it sometimes rewrites, but not always, e.g. if the ap computes in a different way, so sometimes we may have to coerce along it explicitly.
  Id¹-ap : {Δ₁ Δ₂ : Type} (A : Δ₂ → Type) (f : Δ₁ → Δ₂) {δ δ' : Δ₁} (ρ : Id Δ₁ δ δ') (a : A (f δ)) (a' : A (f δ')) →
    Id¹ A (ap f ρ) a a' ≡ Id¹ (λ x → A (f x)) ρ a a'
  -- ap-ap

{-# REWRITE ap-const ap-refl ap-idmap #-}
{-# REWRITE Id¹-ap #-}

postulate
  -- Like Id¹-ap, this should really compute in the other direction
  Id²-ap¹ : {Δ₁ Δ₂ : Type} {Δ₃ : Δ₂ → Type} (A : (x : Δ₂) → Δ₃ x → Type)
            (f : Δ₁ → Δ₂) (g : (x : Δ₁) → Δ₃ (f x)) {δ δ' : Δ₁} (ρ : Id Δ₁ δ δ')
            (a : A (f δ) (g δ)) (a' : A (f δ') (g δ')) →
     Id² A (ap f ρ) (ap g ρ) a a' ≡ Id¹ (λ x → A (f x) (g x)) ρ a a' 
  -- We assert this special case of it separately, since Agda can't rewrite ρ backwards to "ap idmap ρ".
  Id²-ap¹-idmap : {Δ₁ : Type} {Δ₃ : Δ₁ → Type} (A : (x : Δ₁) → Δ₃ x → Type)
            (g : (x : Δ₁) → Δ₃ x) {δ δ' : Δ₁} (ρ : Id Δ₁ δ δ')
            (a : A δ (g δ)) (a' : A δ' (g δ')) →
     Id² A ρ (ap g ρ) a a' ≡ Id¹ (λ x → A x (g x)) ρ a a' 

{-# REWRITE Id²-ap¹ #-}
{-# REWRITE Id²-ap¹-idmap #-}


-- Unit type

record ⊤ : Type where
  constructor ★

postulate
  Id⊤ : (u v : ⊤) → Id ⊤ u v ≡ ⊤

{-# REWRITE Id⊤ #-}

postulate
  refl★ : refl ★ ≡ ★
  -- This is a special case of ap-const
  --ap★ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') → ap {Δ = Δ} {A = λ _ → ⊤} (λ _ → ★) ρ ≡ ★

-- Product types

-- Would it work to derive these from Σ-types?

postulate
  _×_ : Type → Type → Type
  _,_ : {A : Type} {B : Type} → A → B → A × B
  fst : {A : Type} {B : Type} → A × B → A
  snd : {A : Type} {B : Type} → A × B → B

postulate
  βfst : (A : Type) (B : Type) (a : A) (b : B) → fst (a , b) ≡ a
  βsnd : (A : Type) (B : Type) (a : A) (b : B) → snd (a , b) ≡ b
  η, : (A : Type) (B : Type) (u : A × B) → (fst u , snd u) ≡ u
  Id× : (A : Type) (B : Type) (u v : A × B) → Id (A × B) u v ≡ (Id A (fst u) (fst v) × Id B (snd u) (snd v))
  Id¹× : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A B : Δ → Type) (u : A δ × B δ) (v : A δ' × B δ') →
    Id¹ (λ x → A x × B x) ρ u v ≡ (Id¹ A ρ (fst u) (fst v) × Id¹ B ρ (snd u) (snd v))

{-# REWRITE βfst βsnd η, Id× Id¹× #-}

postulate
  refl, : (A : Type) (B : Type) (a : A) (b : B) → refl (a , b) ≡ (refl a , refl b)
  refl-fst : (A : Type) (B : Type) (u : A × B) → refl (fst u) ≡ fst (refl u)
  refl-snd : (A : Type) (B : Type) (u : A × B) → refl (snd u) ≡ snd (refl u)
  ap, : {Δ : Type} (A B : Δ → Type) {δ δ' : Δ} (ρ : Id Δ δ δ') (f : (x : Δ) → A x) (g : (x : Δ) → B x) →
    ap (λ x → (f x , g x)) ρ ≡ (ap f ρ , ap g ρ)
  ap-fst : {Δ : Type} (A B : Δ → Type) {δ δ' : Δ} (ρ : Id Δ δ δ') (f : (x : Δ) → A x × B x) →
    ap (λ x → fst (f x)) ρ ≡ fst (ap f ρ)
  ap-snd : {Δ : Type} (A B : Δ → Type) {δ δ' : Δ} (ρ : Id Δ δ δ') (f : (x : Δ) → A x × B x) →
    ap (λ x → snd (f x)) ρ ≡ snd (ap f ρ)

{-# REWRITE refl, refl-fst refl-snd ap, ap-fst ap-snd #-}

-- Σ-types

postulate
  Σ : (A : Type) → (B : A → Type) → Type
  _﹐_ : {A : Type} {B : A → Type} (a : A) → B a → Σ A B
  π₁ : {A : Type} {B : A → Type} → Σ A B → A
  π₂ : {A : Type} {B : A → Type} (u : Σ A B) → B (π₁ u)

postulate
  βπ₁ : (A : Type) (B : A → Type) (a : A) (b : B a) → π₁ {B = B} (a ﹐ b) ≡ a

{-# REWRITE βπ₁ #-}

postulate
  βπ₂ : (A : Type) (B : A → Type) (a : A) (b : B a) → π₂ {B = B} (a ﹐ b) ≡ b
  η﹐ : (A : Type) (B : A → Type) (u : Σ A B) → (π₁ u ﹐ π₂ u) ≡ u
  IdΣ : (A : Type) (B : A → Type) (u v : Σ A B) → Id (Σ A B) u v ≡ Σ (Id A (π₁ u) (π₁ v)) (λ e → Id¹ B e (π₂ u) (π₂ v))

{-# REWRITE βπ₂ η﹐ IdΣ #-}

postulate
  Id¹Σ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (u : Σ (A δ) (B δ)) (v : Σ (A δ') (B δ')) →
    Id¹ (λ x → Σ (A x) (B x)) ρ u v ≡
    Σ (Id¹ A ρ (π₁ u) (π₁ v)) (λ e → Id² B ρ e (π₂ u) (π₂ v))

{-# REWRITE Id¹Σ #-}

postulate
  refl﹐ : (A : Type) (B : A → Type) (a : A) (b : B a) → refl (_﹐_ {B = B} a b) ≡ (refl a ﹐ refl {A = B a} b)
  reflπ₁ : (A : Type) (B : A → Type) (u : Σ A B) → refl (π₁ u) ≡ π₁ (refl u)
  ap﹐ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
           (u : (x : Δ) → A x) (v : (x : Δ) → B x (u x)) →
           ap {A = λ x → Σ (A x) (B x)} (λ x → (u x ﹐ v x)) ρ ≡ (ap u ρ ﹐ ap v ρ)
  apπ₁ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
           (u : (x : Δ) → Σ (A x) (B x)) → ap (λ x → π₁ (u x)) ρ ≡ π₁ (ap u ρ)

{-# REWRITE refl﹐ reflπ₁ ap﹐ apπ₁ #-}

-- In these two, we have to coerce explicitly, because matching for a rewrite would require rewriting some argument backwards.
postulate
  reflπ₂ : (A : Type) (B : A → Type) (u : Σ A B) → 
    refl (π₂ u) ≡ coe→ (λ X → X) (Id¹-ap B π₁ {δ = u} {δ' = u} (refl u) (π₂ u) (π₂ u)) (π₂ (refl u))  
  apπ₂ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (u : (x : Δ) → Σ (A x) (B x)) →
    ap (λ x → π₂ (u x)) ρ ≡ coe→ (λ X → X) (Id²-ap¹-idmap B (λ x → π₁ (u x)) ρ (π₂ (u δ)) (π₂ (u δ'))) (π₂ (ap u ρ))

{-# REWRITE reflπ₂ apπ₂ #-}

-- Π-types

postulate
  Π : (A : Type) (B : A → Type) → Type
  Λ : {A : Type} {B : A → Type} (f : (x : A) → B x) → Π A B
  _∙_ : {A : Type} {B : A → Type} (f : Π A B) (a : A) → B a

infixl 30 _∙_

postulate
  β∙ : {A : Type} {B : A → Type} (f : (x : A) → B x) (a : A) → (Λ f ∙ a) ≡ f a
  ηΛ : {A : Type} {B : A → Type} (f : Π A B) → Λ (λ x → f ∙ x) ≡ f

{-# REWRITE β∙ ηΛ #-}

postulate
  IdΠ : (A : Type) (B : A → Type) (f g : Π A B) →
    Id (Π A B) f g ≡ Π A (λ a₀ → Π A (λ a₁ → Π (Id A a₀ a₁) (λ a₂ → Id¹ B a₂ (f ∙ a₀) (g ∙ a₁))))

{-# REWRITE IdΠ #-}

postulate
  Id¹Π : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type) (f : Π (A δ) (B δ)) (g : Π (A δ') (B δ')) →
    Id¹ (λ x → Π (A x) (B x)) ρ f g ≡ Π (A δ) (λ a₀ → Π (A δ') (λ a₁ → Π (Id¹ A ρ a₀ a₁) (λ a₂ → Id² B ρ a₂ (f ∙ a₀) (g ∙ a₁))))

{-# REWRITE Id¹Π #-}

postulate
  reflΛ : {A : Type} {B : A → Type} (f : (x : A) → B x) → refl (Λ f) ≡ Λ (λ a₀ → Λ (λ a₁ → Λ (λ a₂ → ap f a₂)))
  refl∙ : {A : Type} {B : A → Type} (f : Π A B) (a : A) → refl (f ∙ a) ≡ refl f ∙ a ∙ a ∙ refl a
  apΛ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type) (f : (x : Δ) (a : A x) → B x a) →
    ap (λ x → Λ (f x)) ρ ≡ Λ λ a₀ → Λ λ a₁ → Λ λ a₂ → ap² f ρ a₂
  ap∙ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (f : (x : Δ) → Π (A x) (B x)) (a : (x : Δ) → A x) →
    ap (λ x → f x ∙ a x) ρ ≡ ap f ρ ∙ (a δ) ∙ (a δ') ∙ (ap a ρ)

{-# REWRITE reflΛ refl∙ apΛ ap∙ #-}

-- Function types

_⟶_ : Type → Type → Type
A ⟶ B = Π A (λ _ → B)

infixr 20 _⟶_

-- Contractibility and 1-1 correspondences

isProp : (A : Type) → Type
isProp A = Π A (λ a₀ → Π A (λ a₁ → Id A a₀ a₁))

isContr : (A : Type) → Type
isContr A = A × isProp A

is11 : {A B : Type} (R : A ⟶ B ⟶ Type) → Type
is11 {A} {B} R = Π A (λ a → isContr (Σ B (λ b → R ∙ a ∙ b))) × Π B (λ b → isContr (Σ A (λ a → R ∙ a ∙ b)))

11Corr : Type → Type → Type
11Corr A B = Σ (A ⟶ B ⟶ Type) is11

postulate
  tr⁰→ : {A : Type} (a₀ : A) → A
  lift⁰→ : {A : Type} (a₀ : A) → Id A a₀ (tr⁰→ a₀)
  tr⁰← : {A : Type} (a₁ : A) → A
  lift⁰← : {A : Type} (a₁ : A) → Id A (tr⁰← a₁) a₁
  utr⁰→ : {A : Type} (a₀ a₁ a₁' : A) (a₂ : Id A a₀ a₁) (a₂' : Id A a₀ a₁') → Id A a₁ a₁'
  ulift⁰→ : {A : Type} (a₀ a₁ a₁' : A) (a₂ : Id A a₀ a₁) (a₂' : Id A a₀ a₁') → Id¹ (λ a → Id A a₀ a) (utr⁰→ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  utr⁰← : {A : Type} (a₁ a₀ a₀' : A) (a₂ : Id A a₀ a₁) (a₂' : Id A a₀' a₁) → Id A a₀ a₀'
  ulift⁰← : {A : Type} (a₁ a₀ a₀' : A) (a₂ : Id A a₀ a₁) (a₂' : Id A a₀' a₁) → Id¹ (λ a → Id A a a₁) (utr⁰← a₁ a₀ a₀' a₂ a₂') a₂ a₂'

postulate
  tr→ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₀ : A δ₀) → A δ₁
  lift→ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₀ : A δ₀) → Id¹ A δ₂ a₀ (tr→ A δ₂ a₀)
  tr← : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₁ : A δ₁) → A δ₀
  lift← : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₁ : A δ₁) → Id¹ A δ₂ (tr← A δ₂ a₁) a₁
  utr→ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₀ : A δ₀)
    (a₁ a₁' : A δ₁) (a₂ : Id¹ A δ₂ a₀ a₁) (a₂' : Id¹ A δ₂ a₀ a₁') → Id (A δ₁) a₁ a₁'
  ulift→ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₀ : A δ₀)
    (a₁ a₁' : A δ₁) (a₂ : Id¹ A δ₂ a₀ a₁) (a₂' : Id¹ A δ₂ a₀ a₁') → Id¹ (λ a → Id¹ A δ₂ a₀ a) (utr→ A δ₂ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  utr← : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₁ : A δ₁)
    (a₀ a₀' : A δ₀) (a₂ : Id¹ A δ₂ a₀ a₁) (a₂' : Id¹ A δ₂ a₀' a₁) → Id (A δ₀) a₀ a₀'
  ulift← : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₁ : A δ₁)
    (a₀ a₀' : A δ₀) (a₂ : Id¹ A δ₂ a₀ a₁) (a₂' : Id¹ A δ₂ a₀' a₁) → Id¹ (λ a → Id¹ A δ₂ a a₁) (utr← A δ₂ a₁ a₀ a₀' a₂ a₂') a₂ a₂'

-- The universe

infixl 30 _↑
infixl 30 _↓

postulate
  _↑ : {A B : Type} → 11Corr A B → Id Type A B
  _↓ : {A B : Type} → Id Type A B → 11Corr A B
  ↑↓ : {A B : Type} (e : 11Corr A B) → e ↑ ↓ ≡ e

{-# REWRITE ↑↓ #-}

postulate
  reflU : (A : Type) → (refl A) ↓ ≡
    ((Λ λ a₀ → Λ λ a₁ → Id A a₀ a₁) ﹐
    ((Λ λ a₀ → (tr⁰→ a₀ ﹐ lift⁰→ a₀) ,
        Λ λ x → Λ λ x' → utr⁰→ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift⁰→ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x')) ,
     (Λ λ a₁ → (tr⁰← a₁ ﹐ lift⁰← a₁) ,
        Λ λ x → Λ λ x' → utr⁰← a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift⁰← a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x'))))
  apU : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) → (ap A δ₂) ↓ ≡
    ((Λ λ a₀ → Λ λ a₁ → Id¹ A δ₂ a₀ a₁) ﹐
    ((Λ λ a₀ → (tr→ A δ₂ a₀ ﹐ lift→ A δ₂ a₀) ,
        Λ λ x → Λ λ x' → utr→ A δ₂ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift→ A δ₂ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x')) ,
      Λ λ a₁ → (tr← A δ₂ a₁ ﹐ lift← A δ₂ a₁) ,
        Λ λ x → Λ λ x' → utr← A δ₂ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift← A δ₂ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x')))

{-# REWRITE reflU apU #-}

-- Computing 1-1 correspondences

-- ...

