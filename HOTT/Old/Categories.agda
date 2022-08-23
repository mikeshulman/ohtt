{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Categories where

open import HOTT.Rewrite hiding (cong; rev)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Sigma.Base
open import HOTT.Groupoids

------------------------------
-- Some more path algebra
------------------------------

cancelR : {A : Type} {a b c : A} {p q : a ＝ b} (r : b ＝ c) →
  (_⊙_ {A} p r ＝ _⊙_ {A} q r) → (p ＝ q)
cancelR {A} {a} {b} {c} {p} {q} = 𝐉 (λ c r → (_⊙_ {A} p r ＝ _⊙_ {A} q r) → (p ＝ q))
  (λ s → begin
           p
         ＝⟨ rev {a ＝ b} (⊙refl {A} p) ⟩
           _⊙_ {A} p (refl b)
         ＝⟨ s ⟩
           _⊙_ {A} q (refl b)
         ＝⟨ ⊙refl {A} q ⟩
           q
         ∎) c

isContr-contraction : {A : Type} (a : A) → (Π[ b ⦂ A ] a ＝ b) → isContr A
isContr-contraction {A} a ctr = (a , (ƛ x ⇒ ƛ y ⇒ _⊙_ {A} (rev {A} (ctr ∙ x)) (ctr ∙ y)))

＝cong-IdF＝ : {A B : Type} (f : A ⇒ B) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b : B)
  (p : f ∙ a₀ ＝ b) (q : f ∙ a₁ ＝ b)
  (e : Id {ε▸ A} (Λ w ⇨ f ∙ top w ＝ b) ([] ∷ a₀ ∷ a₁ ∷ a₂) p q) →
  p ＝ _⊙_ {B} (cong f a₂) q
＝cong-IdF＝ {A} {B} f {a₀} {a₁} a₂ b p q e =
  𝐉 (λ a₁ a₂ → (q : f ∙ a₁ ＝ b) (e : Id {ε▸ A} (Λ w ⇨ f ∙ top w ＝ b) ([] ∷ a₀ ∷ a₁ ∷ a₂) p q) →
       p ＝ _⊙_ {B} (cong f a₂) q) (λ q e → rev {f ∙ a₀ ＝ b}
       (begin
          _⊙_ {B} (cong f (refl a₀)) q
        ＝⟨⟩
          _⊙_ {B} (refl (f ∙ a₀)) q
        ＝⟨ refl⊙ {B} q ⟩
          q
        ＝⟨ rev {f ∙ a₀ ＝ b} e ⟩
          p
        ∎
       )) a₁ a₂ q e

----------------------------------------
-- Initial objects in wild categories
----------------------------------------

-- We prove our general results in a module parametrized by a wild category

module Cat (A : Type)
  (_⟶_ : A → A → Type)
  (_；_ : {a b c : A} → (a ⟶ b) → (b ⟶ c) → (a ⟶ c))
  (id : (a : A) → (a ⟶ a))
  (id； : {a b : A} (f : a ⟶ b) → ((id a ； f) ＝ f))
  (；id : {a b : A} (f : a ⟶ b) → ((f ； id b) ＝ f))
  (；； : {a b c d : A} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) → ((f ； g) ； h) ＝ (f ； (g ； h)))
  where
  
  -- An initial object has a unique morphism to every other object.
  isInit : (a : A) → Type
  isInit a = Π[ b ⦂ A ] isContr (a ⟶ b)

  -- If an object is the vertex of an (incoherent!) cone over the
  -- identity functor, and the component of the cone at itself is the
  -- identity, then it is initial.
  isInit-cone : {a : A}
    (proj : (b : A) → (a ⟶ b))
    (nat : (b c : A) (f : b ⟶ c) → (proj b ； f) ＝ proj c)
    (pid : proj a ＝ id a) →
    isInit a
  isInit-cone {a} proj nat pid = ƛ b ⇒ isContr-contraction (proj b) (ƛ f ⇒
    (begin
      proj b
    ＝⟨ rev {a ⟶ b} (nat _ _ f) ⟩
      (proj a ； f)
    ＝⟨ cong {a ⟶ a} {a ⟶ b} (ƛ g ⇒ (g ； f)) pid ⟩
      (id a ； f)
    ＝⟨ id； f ⟩
      f
    ∎))

  -- We consider how to construct initial objects from "2-coherent
  -- weakly initial" ones: this means they are equipped with a cone
  -- over the identity functor, plus one coherence law for composition
  -- of the cone triangles.
  record wkInit (a : A) : Type where
    field
      proj : (b : A) → (a ⟶ b)
      nat : {b c : A} (f : b ⟶ c) → (proj b ； f) ＝ proj c
      coh : {b c d : A} (f : b ⟶ c) (g : c ⟶ d) →
        _⊙_ {a ⟶ d} (cong {a ⟶ c} (ƛ p ⇒ (p ； g)) (nat f)) (nat g) ＝
        _⊙_ {a ⟶ d} (；； (proj b) f g) (nat (f ； g))
  open wkInit

  -- We will construct initial objects from weakly inital ones by
  -- splitting an idempotent.  It's not possible to split fully
  -- incoherent idempotents (with just idem and I, below) in general,
  -- but one more coherence suffices.
  record qIdem (a : A) : Type where
    field
      idem : a ⟶ a
      I : (idem ； idem) ＝ idem
      J : cong {a ⟶ a} (ƛ f ⇒ (f ； idem)) I ＝ _⊙_ {a ⟶ a} (；； idem idem idem) (cong {a ⟶ a} (ƛ f ⇒ (idem ； f)) I)
  open qIdem

  -- For any weakly initial object, the component of its cone at
  -- itself (which would be the identity for an actual initial object)
  -- is a quasi-idempotent.
  qIdem-wkInit : {a : A} (ai : wkInit a) → qIdem a
  idem (qIdem-wkInit {a} ai) = proj ai a
  I (qIdem-wkInit {a} ai) = nat ai (proj ai a)
  J (qIdem-wkInit {a} ai) =
    let t = proj ai a in
    cancelR {a ⟶ a}
            {p = cong (ƛ⇒ (λ f → f ； t)) (nat ai t)}
            {q = _⊙_ {a ⟶ a} (；； t t t) (cong (ƛ⇒ (_；_ t)) (nat ai t))}
            (nat ai t)
            (begin
              _⊙_ {a ⟶ a} (cong (ƛ⇒ (λ f → f ； t)) (nat ai t)) (nat ai t)
            ＝⟨ coh ai t t ⟩
              _⊙_ {a ⟶ a} (；； t t t) (nat ai (t ； t))
            ＝⟨ cong (ƛ p ⇒ _⊙_ {a ⟶ a} (；； t t t) p)
                    (＝cong-IdF＝ (ƛ⇒ (_；_ (proj ai a))) (nat ai (proj ai a)) (proj ai a)
                                 (nat ai (proj ai a ； proj ai a)) (nat ai (proj ai a))
                                 (refl {Π[ f ⦂ a ⟶ a ] (t ； f) ＝ t} (ƛ f ⇒ nat ai f) ∙ (t ； t) ∙ t ∙ (nat ai t))) ⟩
              _⊙_ {a ⟶ a} (；； t t t)
                (_⊙_ {a ⟶ a}
                  (cong (ƛ⇒ (_；_ t)) (nat ai t))
                  (nat ai t))
            ＝⟨ rev {((t ； t) ； t) ＝ t} (⊙assoc {a ⟶ a}
                   (；； (t) (t) (t))
                   (cong (ƛ⇒ (_；_ (t))) (nat ai (t)))
                   (nat ai (t))) ⟩
              _⊙_ {a ⟶ a} (_⊙_ {a ⟶ a} (；； t t t) (cong (ƛ⇒ (_；_ t)) (nat ai t))) (nat ai t)
             ∎)

  -- What it means to split an idempotent.  Actually we can define a
  -- "splitting" of any endomorphism.
  record splitting {a : A} (i : a ⟶ a) : Type where
    field
      retract : A
      retr : a ⟶ retract
      sect : retract ⟶ a
      isretr : (sect ； retr) ＝ id retract
      isIdem : (retr ； sect) ＝ i

  open splitting

  -- If we have a weakly initial object, and its canonical idempotent
  -- splits, then the splitting object is actually initial.
  init-fromwk : {a : A} (ai : wkInit a) (spl : splitting (proj ai a)) → isInit (retract spl)
  init-fromwk {a} ai spl = isInit-cone
    (λ b → sect spl ； proj ai b)
    (λ b c f →
      (begin
         ((sect spl ； proj ai b) ； f)
       ＝⟨ ；； (sect spl) (proj ai b) f ⟩
         (sect spl ； (proj ai b ； f))
       ＝⟨ cong {a ⟶ c} (ƛ g ⇒ (sect spl ； g)) (nat ai f) ⟩
         (sect spl ； proj ai c)
       ∎))
    (_⊙_ {retract spl ⟶ retract spl} (cong {a ⟶ retract spl} (ƛ g ⇒ (sect spl ； g))
      (begin
        proj ai (retract spl)
      ＝⟨ rev {a ⟶ retract spl} (；id _) ⟩
        proj ai (retract spl) ； id (retract spl)
      ＝⟨ cong (ƛ g ⇒ (proj ai (retract spl) ； g)) (rev {retract spl ⟶ retract spl} (isretr spl)) ⟩
        proj ai (retract spl) ； (sect spl ； retr spl)
      ＝⟨ rev {a ⟶ retract spl} (；； _ _ _) ⟩
        (proj ai (retract spl) ； sect spl) ； retr spl
      ＝⟨ cong (ƛ g ⇒ (g ； retr spl)) (nat ai (sect spl)) ⟩
        proj ai a ； retr spl
      ＝⟨ cong (ƛ g ⇒ (g ； retr spl)) (rev {a ⟶ a} (isIdem spl))  ⟩
        (retr spl ； sect spl) ； retr spl
      ＝⟨ ；； _ _ _ ⟩
        retr spl ； (sect spl ； retr spl)
      ＝⟨ cong (ƛ g ⇒ (retr spl ； g)) (isretr spl) ⟩
        retr spl ； id (retract spl)
      ＝⟨ ；id (retr spl) ⟩
        retr spl
      ∎))
      (isretr spl))

  -- We should be able to construct splittings of idempotents from
  -- countable sequential limits.  Then to apply this in any
  -- particular case, we just have to verify the existence of such
  -- limits, and construct a weakly initial object (usually by an
  -- impredicative "2-coherent wild limit" over the identity functor).
