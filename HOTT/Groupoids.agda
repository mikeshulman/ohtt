{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Groupoids where

open import HOTT.Rewrite using (Type)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Sigma.Base
open import HOTT.Sigma.Transport

infixr 35 _•_
infixl 40 _∘_

------------------------------
-- Path operations
------------------------------

_•_ : {A : Type} {x y z : A} (p : x ＝ y) (q : y ＝ z) → x ＝ z
_•_ {A} {x} {y} {z} p q = comp→ {ε} (Λ _ ⇨ A) [] {x} {x} (refl x) {y} {z} q p

rev : {A : Type} {x y : A} (p : x ＝ y) → (y ＝ x)
rev {A} {x} {y} p = comp→ {ε} (Λ _ ⇨ A) [] {x} {y} p {x} {x} (refl x) (refl x)

cong : {A B : Type} (f : A ⇒ B) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) → (f ∙ a₀ ＝ f ∙ a₁)
cong f {a₀} {a₁} a₂ = refl f ∙ a₀ ∙ a₁ ∙ a₂

------------------------------
-- Equational reasoning
------------------------------

infix  1 begin_
infixr 2 _＝⟨⟩_ _＝⟨_⟩_
infix  3 _∎

data _＝′_ {A : Type} : A → A → Type where
  _∎ : (a : A) → a ＝′ a
  _＝⟨⟩_ : (x : A) {y : A} → (x ＝′ y) → (x ＝′ y)
  _＝⟨_⟩_ : (x : A) {y z : A} → (x ＝ y) → (y ＝′ z) → (x ＝′ z)

begin_ : {A : Type} {x y : A} → (x ＝′ y) → (x ＝ y)
begin x ∎ = refl x
begin x ＝⟨⟩ p = begin p
begin_ {A} (x ＝⟨ p ⟩ q) = _•_ {A} p (begin q)

--------------------------------------------------
-- Propositions and contractibility
--------------------------------------------------

isProp : (A : Type) → Type
isProp A = Π A (λ a₀ → Π A (λ a₁ → (a₀ ＝ a₁)))

isProp-× : {A B : Type} → isProp A → isProp B → isProp (A × B)
isProp-× p q = ƛ x ⇒ ƛ y ⇒ (p ∙ fst x ∙ fst y , q ∙ snd x ∙ snd y)

isContr : (A : Type) → Type
isContr A = A × isProp A

isContr-× : {A B : Type} → isContr A → isContr B → isContr (A × B)
isContr-× (a , p) (b , q) = ((a , b) , isProp-× p q)

isContr-sing : {A : Type} (a : A) → isContr (Σ[ y ﹕ A ] a ＝ y)
isContr-sing {A} a =
  (a , refl a) ,
  (ƛ x ⇒ ƛ y ⇒ utr→ (Λ _ ⇨ A) [] a (fst x) (fst y) (snd x) (snd y) ,
             ulift→ (Λ _ ⇨ A) [] a (fst x) (fst y) (snd x) (snd y))

＝-isContr : {A : Type} (cA : isContr A) (a b : A) → (a ＝ b)
＝-isContr {A} (center , prp) a b = _•_ {A} (prp ∙ a ∙ center) (prp ∙ center ∙ b)

------------------------------
-- Identity elimination
------------------------------

𝐉 : {A : Type} {a : A} (P : (x : A) → (a ＝ x) → Type) (d : P a (refl a))
  (x : A) (e : a ＝ x) → P x e
𝐉 {A} {a} P d x e =
  tr→ {ε▸ (Σ[ x ﹕ A ] a ＝ x)} (Λ z ⇨ P (fst (top z)) (snd (top z)))
       ([] ∷ (a , refl a) ∷ (x , e) ∷ ＝-isContr (isContr-sing a) (a , refl a) (x , e)) d

𝐉β : {A : Type} {a : A} (P : (x : A) → (a ＝ x) → Type) (d : P a (refl a)) →
  𝐉 P d a (refl a) ＝ d
𝐉β {A} {a} P d =
  utr→ {ε▸ (Σ[ x ﹕ A ] a ＝ x)} (Λ z ⇨ P (fst (top z)) (snd (top z)))
        ([] ∷ (a , refl a) ∷ (a , refl a) ∷ ＝-isContr (isContr-sing a) (a , refl a) (a , refl a)) d
        (𝐉 P d a (refl a)) d
        (lift→ {ε▸ (Σ[ x ﹕ A ] a ＝ x)} (Λ z ⇨ P (fst (top z)) (snd (top z)))
          ([] ∷ (a , refl a) ∷ (a , refl a) ∷ ＝-isContr (isContr-sing a) (a , refl a) (a , refl a)) d)
        {!!}

------------------------------
-- 1-1 correspondences
------------------------------

is11 : {A B : Type} (R : A ⇒ B ⇒ Type) → Type
is11 {A} {B} R = Π A (λ a → isContr (Σ B (λ b → R ∙ a ∙ b))) × Π B (λ b → isContr (Σ A (λ a → R ∙ a ∙ b)))

11Corr : Type → Type → Type
11Corr A B = Σ (A ⇒ B ⇒ Type) is11

----------------------------------------
-- Other kinds of equivalences
----------------------------------------

_∘_ : {A B C : Type} (g : B ⇒ C) (f : A ⇒ B) → (A ⇒ C)
g ∘ f = ƛ x ⇒ g ∙ (f ∙ x)

idmap : (A : Type) → (A ⇒ A)
idmap A = ƛ x ⇒ x

QInv : {A B : Type} (f : A ⇒ B) → Type
QInv {A} {B} f = Σ[ g ﹕ B ⇒ A ] (g ∘ f ＝ idmap A) × (f ∘ g ＝ idmap B)

BiInv : {A B : Type} (f : A ⇒ B) → Type
BiInv {A} {B} f = (Σ[ g ﹕ B ⇒ A ] g ∘ f ＝ idmap A) × (Σ[ h ﹕ B ⇒ A ] f ∘ h ＝ idmap B)

QInv→BiInv : {A B : Type} (f : A ⇒ B) → QInv f → BiInv f
QInv→BiInv f (g , sect , retr) = (g , sect) , (g , retr)

BiInv→QInv : {A B : Type} (f : A ⇒ B) → BiInv f → QInv f
BiInv→QInv {A} {B} f ((g , sect) , (h , retr)) = h ,
  (begin
     h ∘ f
   ＝⟨⟩
     idmap A ∘ h ∘ f
   ＝⟨ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ rev {A ⇒ A} {g ∘ f} sect ∙ (h ∙ (f ∙ a₀)) ∙ (h ∙ (f ∙ a₁)) ∙ (cong (h ∘ f) a₂)) ⟩
     g ∘ f ∘ h ∘ f
   ＝⟨ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ cong g (retr ∙ (f ∙ a₀) ∙ (f ∙ a₁) ∙ (cong f a₂))) ⟩
     g ∘ idmap B ∘ f
   ＝⟨⟩
     g ∘ f
   ＝⟨ sect ⟩
     idmap A
   ∎) , retr
