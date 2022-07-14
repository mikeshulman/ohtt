{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --experimental-lossy-unification #-}

module HOTT.Univalence where

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
open import HOTT.Copy.Base
open import HOTT.Universe.Base

infix 35 _≋_ _≃_

----------------------------------------
-- Quasi-invertible maps
----------------------------------------

QInv : {A B : Type} (f : A ⇒ B) → Type
QInv {A} {B} f = Σ[ g ⦂ B ⇒ A ] (g ∘ f ＝ idmap A) × (f ∘ g ＝ idmap B)

_≋_ : Type → Type → Type
A ≋ B = Σ[ f ⦂ A ⇒ B ] QInv f

-- We will prove any quasi-invertible map yields a 1-1 correspondence.
-- One approach to this result is to "adjointify" a quasi-inverse to a
-- half-adjoint equivalence, and use the triangle identities in
-- showing that the desired correspondence is 1-1.  We will instead
-- take a more roundabout route, by way of a bunch of abstract but
-- fairly straightforward categorical properties about quasi-inverses.
-- This may be longer, but it avoids reasoning with 2D paths.

-- Throughout, we must resist the temptation to decompose elements of
-- QInv by pattern-matching on the left side of a definition, as this
-- breaks reduction in cases where the quasi-inverse is not concrete.

-- We first show that quasi-inverses satisfy the 2-out-of-3 property.

∘QInv : {A B C : Type} (f : A ⇒ B) (qf : QInv f) (g : B ⇒ C) (qg : QInv g) → QInv (g ∘ f)
∘QInv f qf g qg =
  let f⁻¹ = fst qf
      fsect = fst (snd qf)
      fretr = snd (snd qf) in
  let g⁻¹ = fst qg
      gsect = fst (snd qg)
      gretr = snd (snd qg) in
  f⁻¹ ∘ g⁻¹ ,
  funext (ƛ x ⇒ cong f⁻¹ (happly gsect (f ∙ x)) ⊙ happly fsect x) ,
  funext (ƛ y ⇒ cong g (happly fretr (g⁻¹ ∙ y)) ⊙ happly gretr y)

_∘≋_ : {A B C : Type} (g : B ≋ C) (f : A ≋ B) → A ≋ C
g ∘≋ f = (fst g ∘ fst f , ∘QInv (fst f) (snd f) (fst g) (snd g))

∘QInv-cancelR : {A B C : Type} (f : A ⇒ B) (qf : QInv f) (g : B ⇒ C) (qgf : QInv (g ∘ f)) → QInv g
∘QInv-cancelR f qf g qgf =
  let gf⁻¹ = fst qgf
      gfsect = fst (snd qgf)
      gfretr = snd (snd qgf) in
  let f⁻¹ = fst qf
      fsect = fst (snd qf)
      fretr = snd (snd qf) in
  (ƛ z ⇒ f ∙ (gf⁻¹ ∙ z)) ,
  funext (ƛ y ⇒ (begin
                   f ∙ (gf⁻¹ ∙ (g ∙ y))
                 ＝⟨ cong (f ∘ gf⁻¹ ∘ g) (rev (happly fretr y)) ⟩
                   f ∙ (gf⁻¹ ∙ (g ∙ (f ∙ (f⁻¹ ∙ y))))
                 ＝⟨ cong f (happly gfsect (f⁻¹ ∙ y)) ⟩
                   f ∙ (f⁻¹ ∙ y)
                 ＝⟨ happly fretr y ⟩
                   y
                 ∎)) ,
  funext (ƛ z ⇒ happly gfretr z)

∘QInv-cancelL : {A B C : Type} (f : A ⇒ B) (g : B ⇒ C) (qg : QInv g) (qgf : QInv (g ∘ f)) → QInv f
∘QInv-cancelL f g qg qgf =
  let gf⁻¹ = fst qgf
      gfsect = fst (snd qgf)
      gfretr = snd (snd qgf) in
  let g⁻¹ = fst qg
      gsect = fst (snd qg)
      gretr = snd (snd qg) in
  (ƛ y ⇒ gf⁻¹ ∙ (g ∙ y)) ,
  funext (ƛ x ⇒ happly gfsect x) ,
  funext (ƛ y ⇒ (begin
                   f ∙ (gf⁻¹ ∙ (g ∙ y))
                 ＝⟨ rev (happly gsect (f ∙ (gf⁻¹ ∙ (g ∙ y)))) ⟩
                   g⁻¹ ∙ (g ∙ (f ∙ (gf⁻¹ ∙ (g ∙ y))))
                 ＝⟨ cong g⁻¹ (happly gfretr (g ∙ y)) ⟩
                   g⁻¹ ∙ (g ∙ y)
                 ＝⟨ happly gsect y ⟩
                   y
                 ∎))

-- Similarly, they satisfy the 2-out-of-6 property.  We will only need
-- 1/4 of the full 2-out-of-6 property.
∘QInv-2/6 : {A B C D : Type} (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D)
  (qgf : QInv (g ∘ f)) (qhg : QInv (h ∘ g)) →
  QInv f
∘QInv-2/6 f g h qgf qhg =
  let gf⁻¹ = fst qgf
      gfsect = fst (snd qgf)
      gfretr = snd (snd qgf) in
  let hg⁻¹ = fst qhg
      hgsect = fst (snd qhg)
      hgretr = snd (snd qhg) in
  (ƛ y ⇒ gf⁻¹ ∙ (g ∙ y)) ,
  funext (ƛ x ⇒ happly gfsect x) ,
  funext (ƛ y ⇒ (begin
                   f ∙ (gf⁻¹ ∙ (g ∙ y))
                 ＝⟨ rev (happly hgsect _) ⟩
                   hg⁻¹ ∙ (h ∙ (g ∙ (f ∙ (gf⁻¹ ∙ (g ∙ y)))))
                 ＝⟨ cong (hg⁻¹ ∘ h) (happly gfretr (g ∙ y)) ⟩
                   hg⁻¹ ∙ (h ∙ (g ∙ y))
                 ＝⟨ happly hgsect y ⟩
                   y
                 ∎))

-- Concatenating identifications on either side is quasi-invertible,
-- since you can concatenate with the reverse.
⊙QInvR : {A : Type} (x : A) {y z : A} (q : y ＝ z) → QInv (ƛ p ⇒ _⊙_ {A} {x} p q)
⊙QInvR x {y} {z} q = (ƛ r ⇒ r ⊙ rev q) ,
  funext (ƛ p ⇒ (begin
                   (p ⊙ q) ⊙ rev q
                 ＝⟨ ⊙assoc p q (rev q) ⟩
                   p ⊙ (q ⊙ rev q)
                 ＝⟨ cong (ƛ r ⇒ p ⊙ r) (⊙rev q) ⟩
                   p ⊙ refl y
                 ＝⟨ ⊙refl p ⟩
                   p
                 ∎)) ,
  funext (ƛ r ⇒ (begin
                   (r ⊙ rev q) ⊙ q
                 ＝⟨ ⊙assoc r (rev q) q ⟩
                   r ⊙ (rev q ⊙ q)
                 ＝⟨ cong (ƛ p ⇒ r ⊙ p) (rev⊙ q) ⟩
                   r ⊙ refl z
                 ＝⟨ ⊙refl r ⟩
                   r
                 ∎))

⊙QInvL : {A : Type} {x y : A} (z : A) (p : x ＝ y) → QInv (ƛ q ⇒ _⊙_ {A} {x} {y} {z} p q)
⊙QInvL {A} {x} {y} z p = (ƛ r ⇒ rev p ⊙ r) ,
  funext (ƛ q ⇒ (begin
                   rev p ⊙ (p ⊙ q)
                 ＝⟨ rev (⊙assoc (rev p) p q) ⟩
                   (rev p ⊙ p) ⊙ q
                 ＝⟨ cong (ƛ r ⇒ r ⊙ q) (rev⊙ p) ⟩
                   refl _ ⊙ q
                 ＝⟨ refl⊙ q ⟩
                   q
                 ∎)) ,
  funext (ƛ r ⇒ (begin
                   p ⊙ (rev p ⊙ r)
                 ＝⟨ rev (⊙assoc p (rev p) r) ⟩
                   (p ⊙ rev p) ⊙ r
                 ＝⟨ cong (ƛ q ⇒ q ⊙ r) (⊙rev p) ⟩
                   refl _ ⊙ r
                 ＝⟨ refl⊙ r ⟩
                   r
                 ∎))

-- Anything equal to the identity map is quasi-invertible.
QInv-idmap : (A : Type) → QInv (idmap A)
QInv-idmap A = idmap A , refl (idmap A) , refl (idmap A)

≋-idmap : (A : Type) → (A ≋ A)
≋-idmap A = (idmap A , QInv-idmap A)

QInv-cong-＝idmap : {A : Type} (f : A ⇒ A) (p : idmap A ＝ f) (a₀ a₁ : A) → QInv (refl f ∙ a₀ ∙ a₁)
QInv-cong-＝idmap f p a₀ a₁ = 𝐉 (λ f p → QInv (refl f ∙ a₀ ∙ a₁)) (QInv-idmap _) f p

-- The action on identifications of a quasi-invertible map is
-- quasi-invertible.  The slick proof of this using the 2-out-of-6
-- property hearkens back to the proof in classical algebraic topology
-- that a homotopy equivalence is a weak homotopy equivalence
-- (i.e. induces an isomorphism on all homotopy groups *with all
-- basepoints* -- the homotopy equivalence is not based).
QInv-＝ : {A B : Type} (f : A ⇒ B) (qf : QInv f) (a₀ a₁ : A) →
  QInv (refl f ∙ a₀ ∙ a₁)
QInv-＝ f qf a₀ a₁ =
  let g = fst qf
      sect = fst (snd qf)
      retr = snd (snd qf) in
  ∘QInv-2/6 (refl f ∙ a₀ ∙ a₁) (refl g ∙ (f ∙ a₀) ∙ (f ∙ a₁)) (refl f ∙ (g ∙ (f ∙ a₀)) ∙ (g ∙ (f ∙ a₁)))
    (QInv-cong-＝idmap (g ∘ f) (rev sect) a₀ a₁)
    (QInv-cong-＝idmap (f ∘ g) (rev retr) (f ∙ a₀) (f ∙ a₁))

-- Being a proposition transfers across quasi-inverses.
isProp-QInv : {A B : Type} → (A ≋ B) → isProp A → isProp B
isProp-QInv {A} {B} qi pA = ƛ b₀ ⇒ ƛ b₁ ⇒
  let f = fst qi
      g = fst (snd qi)
      sect = fst (snd (snd qi))
      retr = snd (snd (snd qi)) in
  (begin
    b₀
  ＝⟨ rev (happly retr b₀) ⟩
    f ∙ (g ∙ b₀)
  ＝⟨ cong f (pA ∙ (g ∙ b₀) ∙ (g ∙ b₁)) ⟩
    f ∙ (g ∙ b₁)
  ＝⟨ happly retr b₁  ⟩
    b₁
  ∎)

-- This is a crucial lemma: if f and g are quasi-inverses, then they
-- are "adjoint" with respect to identification types: (f a ＝ b) is
-- equivalent to (a ＝ g b).
QInv-＝-adjoint : {A B : Type} (f : A ⇒ B) (qf : QInv f) (a : A) (b : B) →
  (a ＝ fst qf ∙ b) ≋ (f ∙ a ＝ b)
QInv-＝-adjoint {A} {B} f qf a b =
  let g = fst qf
      sect = fst (snd qf)
      retr = snd (snd qf) in
  (ƛ p ⇒ cong f p ⊙ (happly retr b)) ,
  ∘QInv (refl f ∙ a ∙ (g ∙ b)) (QInv-＝ f (g , sect , retr) a (g ∙ b))
        (ƛ p ⇒ p ⊙ happly retr b) (⊙QInvR (f ∙ a) (happly retr b))

-- Σ-types are functorial on fiberwise quasi-inverses.
total : {A : Type} {B C : A → Type} (f : (x : A) → B x ⇒ C x) → Σ A B ⇒ Σ A C
total f = (ƛ w ⇒ fst w , f (fst w) ∙ (snd w))

QInv-total : {A : Type} (B C : A → Type) (f : (x : A) → B x ⇒ C x) (e : (x : A) → QInv (f x)) →
  QInv {Σ A B} {Σ A C} (total f)
QInv-total {A} B C f e = (ƛ w ⇒ fst w , fst (e (fst w)) ∙ (snd w)) ,
  funext (ƛ w ⇒ refl (fst w) ,
    coe← (Id-REFL[]▸ (Λ _ ⇨ A) (Λ z ⇨ B (top z)) (fst w) (fst (e (fst w)) ∙ (f (fst w) ∙ snd w)) (snd w))
         (happly (fst (snd (e (fst w)))) (snd w))) ,
  funext (ƛ w ⇒ refl (fst w) ,
    coe← (Id-REFL[]▸ (Λ _ ⇨ A) (Λ z ⇨ C (top z)) (fst w) (f (fst w) ∙ (fst (e (fst w)) ∙ snd w)) (snd w))
         (happly (snd (snd (e (fst w)))) (snd w)))

≋-total : {A : Type} (B C : A → Type) (f : (x : A) → (B x ≋ C x)) →
  (Σ A B) ≋ (Σ A C)
≋-total {A} B C f = (ƛ w ⇒ fst w , fst (f (fst w)) ∙ (snd w)) , QInv-total B C (λ x → fst (f x)) (λ x → snd (f x))

-- Any map between contractible types is quasi-invertible.
QInv-contr : {A B : Type} (f : A ⇒ B) (cA : isContr A) (cB : isContr B) → QInv f
QInv-contr f cA cB = (ƛ b ⇒ fst cA) , funext (ƛ a ⇒ snd cA ∙ _ ∙ a) , funext (ƛ b ⇒ snd cB ∙ _ ∙ b)

≋-Σ-over-contr : {A : Type} (B : A ⇒ Type) (cA : isContr A) →
  (Σ[ x ⦂ A ] B ∙ x) ≋ (B ∙ fst cA)
≋-Σ-over-contr B cA =
  (ƛ s ⇒ tr⇒ B (snd cA ∙ fst s ∙ fst cA) (snd s)) ,
  (ƛ b ⇒ (fst cA , b)) ,
  rev (funext (ƛ s ⇒ snd cA ∙ fst s ∙ fst cA ,
    lift→ {ε▸ _} (Λ x ⇨ B ∙ top x) ([] ∷ fst s ∷ fst cA ∷ (snd cA ∙ fst s ∙ fst cA)) (snd s))) ,
  funext (ƛ b ⇒ tr⇒＝refl B {fst cA} (snd cA ∙ fst cA ∙ fst cA) (isProp-＝ (snd cA) (fst cA) (fst cA) ∙ _ ∙ _) b)

-- Finally, we can prove that every quasi-invertible map yields a 1-1
-- correspondence.  The correspondence is (f a ＝ b), and it's easy to
-- prove that this is 1-1 on one side since it's a based path-space.
-- For the other side, we use the adjointness property above to
-- rewrite (f a ＝ b) as (a ＝ g b), where g is the quasi-inverse, and
-- apply based path contractibility again.
QInv→11 : {A B : Type} (f : A ⇒ B) (fe : QInv f) → 11Corr A B
QInv→11 {A} {B} f qf =
  let g = fst qf
      sect = fst (snd qf)
      retr = snd (snd qf) in
  f , g , (ƛ a ⇒ ƛ b ⇒ f ∙ a ＝ b) ,
  (ƛ a ⇒ refl (f ∙ a)) , (ƛ b ⇒ retr ∙ b ∙ b ∙ refl b) ,
  (ƛ a ⇒ isProp-sing→ (f ∙ a)) ,
  (ƛ b ⇒ isProp-QInv (≋-total (λ a → a ＝ g ∙ b) (λ a → f ∙ a ＝ b) (λ a → QInv-＝-adjoint f (g , sect , retr) a b))
                     (isProp-sing← (g ∙ b)))

----------------------------------------
-- Univalence for quasi-inverses
----------------------------------------

ua : {A B : Type} (f : A ≋ B) → (A ＝ B)
ua f = QInv→11 (fst f) (snd f) ↑

QInv-coe⇒ : {A B : Type} (e : A ＝ B) → QInv (coe⇒ e)
QInv-coe⇒ e = (coe⇐ e ,
  funext (ƛ a ⇒ ucoe⇐ e (coe⇒ e ∙ a) (coe⇐ e ∙ (coe⇒ e ∙ a)) a (~coe⇐ e (coe⇒ e ∙ a)) (~coe⇒ e a)) ,
  funext (ƛ b ⇒ ucoe⇒ e (coe⇐ e ∙ b) (coe⇒ e ∙ (coe⇐ e ∙ b)) b (~coe⇒ e (coe⇐ e ∙ b)) (~coe⇐ e b)))

--------------------------------------------------
-- Pre- and post-composition quasi-inverses
--------------------------------------------------

QInv-post∘ : {A B C : Type} (f : B ⇒ C) (qf : QInv f) → QInv {A ⇒ B} {A ⇒ C} (ƛ g ⇒ f ∘ g)
QInv-post∘ {A} {B} {C} f qf =
  let f⁻¹ = fst qf
      fsect = fst (snd qf)
      fretr = snd (snd qf) in
  (ƛ h ⇒ f⁻¹ ∘ h) ,
  funext {f = ƛ g ⇒ f⁻¹ ∘ f ∘ g} {g = idmap (A ⇒ B)}
    (ƛ g ⇒ funext {f = f⁻¹ ∘ f ∘ g} {g} (ƛ x ⇒ happly {f = f⁻¹ ∘ f} {g = idmap B} fsect (g ∙ x))) ,
  funext {f = ƛ h ⇒ f ∘ f⁻¹ ∘ h} {g = idmap (A ⇒ C)}
    (ƛ h ⇒ funext {f = f ∘ f⁻¹ ∘ h} {h} (ƛ x ⇒ happly {f = f ∘ f⁻¹} {g = idmap C} fretr (h ∙ x))) 

QInv-pre∘ : {A B C : Type} (f : A ⇒ B) (qf : QInv f) → QInv {B ⇒ C} {A ⇒ C} (ƛ g ⇒ g ∘ f)
QInv-pre∘ {A} {B} {C} f qf =
  let f⁻¹ = fst qf
      fsect = fst (snd qf)
      fretr = snd (snd qf) in
  (ƛ h ⇒ h ∘ f⁻¹) ,
  funext {f = ƛ g ⇒ g ∘ f ∘ f⁻¹} {g = idmap (B ⇒ C)}
    (ƛ g ⇒ funext {f = g ∘ f ∘ f⁻¹} {g} (ƛ x ⇒ cong g (happly {f = f ∘ f⁻¹} {g = idmap B} fretr x))) ,
  funext {f = ƛ h ⇒ h ∘ f⁻¹ ∘ f} {g = idmap (A ⇒ C)}
    (ƛ h ⇒ funext {f = h ∘ f⁻¹ ∘ f} {h} (ƛ x ⇒ cong h (happly {f = f⁻¹ ∘ f} {g = idmap A} fsect x)))

----------------------------------------
-- QInv equational reasoning
----------------------------------------

infix  1 begin≋_
infixr 2 _≋⟨⟩_ _≋⟨_⟩_ _≡⟨_⟩_
infix  3 _∎

data _≋′_ : Type → Type → Typeᵉ where
  _∎ : (a : Type) → a ≋′ a
  _≋⟨⟩_ : (x : Type) {y : Type} → (x ≋′ y) → (x ≋′ y)
  _≋⟨_⟩_ : (x : Type) {y z : Type} → (x ≋ y) → (y ≋′ z) → (x ≋′ z)
  _≡⟨_⟩_ : (x : Type) {y z : Type} → (x ≡ y) → (y ≋′ z) → (x ≋′ z)

begin≋_ : {x y : Type} → (x ≋′ y) → (x ≋ y)
begin≋ x ∎ = ≋-idmap x
begin≋ x ≋⟨⟩ p = begin≋ p
begin≋_ (x ≋⟨ p ⟩ q) = (begin≋ q) ∘≋ p
begin≋ x ≡⟨ reflᵉ ⟩ q = begin≋ q

----------------------------------------
-- Contractible fibers
----------------------------------------

fibContr : {A B : Type} (f : A ⇒ B) → Type
fibContr {A} {B} f = Π[ y ⦂ B ] isContr (Σ[ x ⦂ A ] f ∙ x ＝ y)

isProp-fibContr : {A B : Type} (f : A ⇒ B) → isProp (fibContr f)
isProp-fibContr f = isProp-Π (λ y → isProp-isContr _)

-- We already proved this!
QInv→fibContr : {A B : Type} (f : A ⇒ B) (qf : QInv f) → fibContr f
QInv→fibContr f qf = ƛ y ⇒ (fst qf ∙ y , happly (snd (snd qf)) y) , (snd (snd (snd (snd (snd (snd (QInv→11 f qf))))))) ∙ y 

fibContr→QInv : {A B : Type} (f : A ⇒ B) (qf : fibContr f) → QInv f
fibContr→QInv f qf = (ƛ b ⇒ fst (fst (qf ∙ b))) ,
  funext (ƛ a ⇒ fst (snd (qf ∙ (f ∙ a)) ∙ (fst (qf ∙ (f ∙ a))) ∙ (a , refl (f ∙ a)))) ,
  funext (ƛ b ⇒ snd (fst (qf ∙ b)))

fib-total : {A : Type} {B C : A → Type} (f : (x : A) → B x ⇒ C x) (v : Σ A C) →
  (Σ[ u ⦂ Σ A B ] total f ∙ u ＝ v) ＝ (Σ[ b ⦂ B (fst v) ] f (fst v) ∙ b ＝ snd v)
fib-total {A} {B} {C} f v =
  ua (begin≋
    Σ[ u ⦂ Σ A B ] total f ∙ u ＝ v
  ≋⟨⟩
    Σ[ u ⦂ Σ A B ] Σ[ e ⦂ fst u ＝ fst v ] Id (Λ x ⇨ C (top x)) ([] ∷ fst u ∷ fst v ∷ e) (f (fst u) ∙ snd u) (snd v)
  ≋⟨ (ƛ uew ⇒ (fst (fst uew) , fst (snd uew)) , snd (fst uew) , snd (snd uew)) ,
     (ƛ qbw ⇒ (fst (fst qbw) , fst (snd qbw)) , snd (fst qbw) , snd (snd qbw)) ,
     refl _ , refl _ ⟩
    Σ[ q ⦂ (Σ[ a ⦂ A ] a ＝ fst v) ] Σ[ b ⦂ B (fst q) ] Id {ε▸ A} (Λ x ⇨ C (top x)) ([] ∷ fst q ∷ fst v ∷ snd q) (f (fst q) ∙ b) (snd v)
  ≋⟨ ≋-Σ-over-contr (ƛ q ⇒ Σ[ b ⦂ B (fst q) ] Id {ε▸ A} (Λ x ⇨ C (top x)) ([] ∷ fst q ∷ fst v ∷ snd q) (f (fst q) ∙ b) (snd v))
                    (isContr-sing← (fst v)) ⟩
    Σ[ b ⦂ B (fst v) ] Id {ε▸ A} (Λ x ⇨ C (top x)) ([] ∷ fst v ∷ fst v ∷ fst (refl v)) (f (fst v) ∙ b) (snd v)
  ≡⟨ congᶠ (Σ (B (fst v))) (funextᵉ (λ b → Id-REFL[]▸ (Λ _ ⇨ A) (Λ x ⇨ C (top x)) (fst v) _ _ )) ⟩
    Σ[ b ⦂ B (fst v) ] f (fst v) ∙ b ＝ snd v
  ∎)

fibContr-of-total : {A : Type} {B C : A → Type} (f : (x : A) → B x ⇒ C x) →
  (fibContr {Σ A B} {Σ A C} (total f)) →
  (a : A) → fibContr (f a)
fibContr-of-total f fcf a = ƛ y ⇒ tr⇒ (ƛ X ⇒ isContr X) (fib-total f (a , y)) (fcf ∙ (a , y))

QInv-of-total : {A : Type} {B C : A → Type} (f : (x : A) → B x ⇒ C x) →
  (QInv {Σ A B} {Σ A C} (total f)) →
  (a : A) → QInv (f a)
QInv-of-total f fcf a = fibContr→QInv (f a) (fibContr-of-total f (QInv→fibContr (total f) fcf) a)

----------------------------------------
-- Bi-invertible maps
----------------------------------------

-- It might be better in principle to use half-adjoint equivalences,
-- but bi-invertible maps are easier to show to be a proposition.

BiInv : {A B : Type} (f : A ⇒ B) → Type
BiInv {A} {B} f = (Σ[ g ⦂ B ⇒ A ] g ∘ f ＝ idmap A) × (Σ[ h ⦂ B ⇒ A ] f ∘ h ＝ idmap B)

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

isProp-BiInv : {A B : Type} (f : A ⇒ B) → isProp (BiInv f)
isProp-BiInv f = isProp-from-inhab (λ biinv →
  let qf = BiInv→QInv f biinv in
  isProp-×
    (isProp-QInv
      (≋-total (λ g → g ＝ fst qf) (λ g → g ∘ f ＝ idmap _) (λ g →
        QInv-＝-adjoint (ƛ g ⇒ g ∘ f) (QInv-pre∘ f qf) g (idmap _)))
      (isProp-sing← (fst qf)))
    (isProp-QInv
      (≋-total (λ h → h ＝ fst qf) (λ h → f ∘ h ＝ idmap _) (λ h →
        QInv-＝-adjoint (ƛ h ⇒ f ∘ h) (QInv-post∘ f qf) h (idmap _)))
      (isProp-sing← (fst qf))))

_≃_ : Type → Type → Type
A ≃ B = Σ[ f ⦂ A ⇒ B ] BiInv f

----------------------------------------
-- Voevodsky-style univalence
----------------------------------------

ua≃ : (A B : Type) → (A ≃ B) ⇒ (A ＝ B)
ua≃ A B = ƛ f ⇒ ua (fst f , BiInv→QInv (fst f) (snd f))

Σua≃ : (A : Type) → (Σ[ B ⦂ Type ] A ≃ B) ⇒ (Σ[ B ⦂ Type ] A ＝ B)
Σua≃ A = total (ua≃ A)

coe≃ : (A B : Type) → (A ＝ B) ⇒ (A ≃ B)
coe≃ A B = ƛ e ⇒ (coe⇒ e , QInv→BiInv (coe⇒ e) (QInv-coe⇒ e))

Σcoe≃ : (A : Type) → (Σ[ B ⦂ Type ] A ＝ B) ⇒ (Σ[ B ⦂ Type ] A ≃ B)
Σcoe≃ A = total (coe≃ A)

retr-ua≃ : (A B : Type) → coe≃ A B ∘ ua≃ A B ＝ idmap (A ≃ B)
retr-ua≃ A B = funext (ƛ e ⇒ refl (fst e) ,
  Id-prop (refl (fst e)) BiInv isProp-BiInv
    (QInv→BiInv (coe⇒ (ua≃ A B ∙ e)) (QInv-coe⇒ (ua≃ A B ∙ e)))
    (snd e))

retr-Σua≃ : (A : Type) → Σcoe≃ A ∘ Σua≃ A ＝ idmap _
retr-Σua≃ A = Σ-retract (A ≃_) (A ＝_) (ua≃ A) (coe≃ A) (retr-ua≃ A)

isContr-Σ≃ : (A : Type) → isContr (Σ[ B ⦂ Type ] A ≃ B)
isContr-Σ≃ A = isContr-retract (Σua≃ A) (Σcoe≃ A) (retr-Σua≃ A) (isContr-sing→ A)

QInv-Σcoe≃ : (A : Type) → QInv (Σcoe≃ A)
QInv-Σcoe≃ A = QInv-contr (Σcoe≃ A) (isContr-sing→ A) (isContr-Σ≃ A)

-- Finally, we have Voevodsky-style univalence (stated with BiInv instead of fibContr).
QInv-coe≃ : (A B : Type) → QInv (coe≃ A B)
QInv-coe≃ A B = QInv-of-total (coe≃ A) (QInv-Σcoe≃ A) B
