{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Bool where

open import HOTT.Rewrite using (Type; _β‘_)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Indices
open import HOTT.Sigma.Base
open import HOTT.Pi.Base
open import HOTT.Sum.Base
open import HOTT.Unit
open import HOTT.Empty
open import HOTT.Indices
open import HOTT.Groupoids
open import HOTT.Univalence
open import HOTT.Decidable


infix 35 _οΌπ_

------------------------------
-- Generalized booleans
------------------------------

data bool (Ξ© : Type) (f t : Ξ©) : Ξ© β Type where
  false : bool Ξ© f t f
  true : bool Ξ© f t t

bool-case : {Ξ© : Type} {f t : Ξ©} (P : (x : Ξ©) β bool Ξ© f t x β Type)
  (then : P t true) (else : P f false)
  {Ο : Ξ©} (b : bool Ξ© f t Ο) β P Ο b
bool-case P then else false = else
bool-case P then else true = then

------------------------------
-- Ordinary booleans
------------------------------

data π : Type where
  false : π
  true : π

π-case : (P : π β Type) (then : P true) (else : P false) (b : π) β P b
π-case P then else false = else
π-case P then else true = then

----------------------------------------
-- Equality of ordinary booleans
----------------------------------------

data _οΌπ_ : π β π β Type where
  false : false οΌπ false
  true : true οΌπ true

οΌπ-case : (P : (u v : π) β (u οΌπ v) β Type) (then : P true true true) (else : P false false false)
  {u v : π} (b : u οΌπ v) β P u v b
οΌπ-case P then else false = else
οΌπ-case P then else true = then

------------------------------
-- Special path operations
------------------------------

reflπ : (n : π) β (n οΌ n)
reflπ n = refl n

revπ : {m n : π} β (m οΌ n) β (n οΌ m)
revπ p = rev {π} p

_βπ_ : {x y z : π} β (x οΌ y) β (y οΌ z) β x οΌ z
p βπ q = _β_ {π} p q

reflοΌπ : {m n : π} (p : m οΌ n) β (p οΌ p)
reflοΌπ p = refl p

revοΌπ : {m n : π} {p q : m οΌ n} β (p οΌ q) β (q οΌ p)
revοΌπ {m} {n} r = rev {m οΌ n} r

_βοΌπ_ : {m n : π} {x y z : m οΌ n} β (x οΌ y) β (y οΌ z) β x οΌ z
_βοΌπ_ {m} {n} p q = _β_ {m οΌ n} p q

------------------------------
-- Identity types
------------------------------

postulate
  οΌ-bool : (Ξ© : Type) (f t : Ξ©) (Ο : Ξ©) (u v : bool Ξ© f t Ο) β
    (u οΌ v) β‘
    bool (οΌIdx Ξ© (bool Ξ© f t))
      (f , f , refl f , false , false) (t , t , refl t , true , true)
      (Ο , Ο , refl Ο , u , v)
  Id-bool : {Ξ : Tel} (Ξ© : el Ξ β Type) (f t : (x : el Ξ) β Ξ© x)
    (Ο : (x : el Ξ) β Ξ© x) (Ξ΄ : el (ID Ξ))
    (uβ : bool (Ξ© (Ξ΄ β)) (f (Ξ΄ β)) (t (Ξ΄ β)) (Ο (Ξ΄ β)))
    (uβ : bool (Ξ© (Ξ΄ β)) (f (Ξ΄ β)) (t (Ξ΄ β)) (Ο (Ξ΄ β))) β
    Id (Ξ x β¨ bool (Ξ© x) (f x) (t x) (Ο x)) Ξ΄ uβ uβ β‘
    bool (Id-Idx Ξ΄ Ξ© (Ξ» x y β bool (Ξ© x) (f x) (t x) y))
      (f (Ξ΄ β) , f (Ξ΄ β) , ap (Ξβ¨ Ξ©) f Ξ΄ , false , false )
      (t (Ξ΄ β) , t (Ξ΄ β) , ap (Ξβ¨ Ξ©) t Ξ΄ , true , true)
      (Ο (Ξ΄ β) , Ο (Ξ΄ β) , ap (Ξβ¨ Ξ©) Ο Ξ΄ , uβ , uβ)
  οΌ-π : (u v : π) β (u οΌ v) β‘ (u οΌπ v)

{-# REWRITE οΌ-bool Id-bool οΌ-π #-}

postulate
  οΌ-οΌπ : (nβ nβ : π) (eβ eβ : nβ οΌπ nβ) β
    (eβ οΌ eβ) β‘
    bool (Ξ£[ xβ β¦ π ] Ξ£[ xβ β¦ π ] (xβ οΌ xβ) Γ (xβ οΌ xβ))
      (false , false , false , false)
      (true , true , true , true)
      (nβ , nβ , eβ , eβ)
  Id-οΌπ : {Ξ : Tel} (Ξ΄ : el (ID Ξ)) (nβ nβ : el Ξ β π)
    (eβ : nβ (Ξ΄ β) οΌπ nβ (Ξ΄ β)) (eβ : nβ (Ξ΄ β) οΌπ nβ (Ξ΄ β)) β
    Id {Ξ} (Ξ x β¨ nβ x οΌπ nβ x) Ξ΄ eβ eβ β‘
    bool (Ξ£[ xββ β¦ π ] Ξ£[ xββ β¦ π ] Ξ£[ xββ β¦ xββ οΌ xββ ]
          Ξ£[ xββ β¦ π ] Ξ£[ xββ β¦ π ] Ξ£[ xββ β¦ xββ οΌ xββ ]
          (xββ οΌπ xββ) Γ (xββ οΌπ xββ))
      (false , false , false , false , false , false , false , false)
      (true , true , true , true , true , true , true , true)
      (nβ (Ξ΄ β) , nβ (Ξ΄ β) , ap (Ξ _ β¨ π) nβ Ξ΄ ,
       nβ (Ξ΄ β) , nβ (Ξ΄ β) , ap (Ξ _ β¨ π) nβ Ξ΄ ,
       eβ , eβ)

{-# REWRITE οΌ-οΌπ Id-οΌπ #-}

------------------------------
-- Negation
------------------------------

Β¬ : π β π
Β¬ = Ζ x β π-case (Ξ» _ β π) false true x

Β¬Β¬ : Β¬ β Β¬ οΌ idmap π
Β¬Β¬ = funext {f = Β¬ β Β¬} {g = idmap π}
  (Ζ x β π-case (Ξ» x β Β¬ β (Β¬ β x) οΌ x) true false x)

QInv-Β¬ : QInv Β¬
QInv-Β¬ = Β¬ , Β¬Β¬ , Β¬Β¬

11-Β¬ : 11Corr π π
11-Β¬ = QInvβ11 Β¬ QInv-Β¬

----------------------------------------
-- Decidable equality and sethood
----------------------------------------

π-code : π β π β Type
π-code = π-case (Ξ» x β (y : π) β Type) (π-case (Ξ» y β Type) β€ β₯) (π-case (Ξ» y β Type) β₯ β€)

trueβ false : (_οΌ_ {π} true false) β β₯
trueβ false = Ζ e β οΌπ-case (Ξ» x y _ β π-code x y) β β e

falseβ true : (_οΌ_ {π} false true) β β₯
falseβ true = Ζ e β οΌπ-case (Ξ» x y _ β π-code x y) β β e

deceq-π : DecEq π
deceq-π = Ζ x β Ζ y β
  π-case (Ξ» a β (a οΌ y) β ((a οΌ y) β β₯))
    (π-case (Ξ» b β (true οΌ b) β ((true οΌ b) β β₯)) (inl true) (inr trueβ false) y)
    (π-case (Ξ» b β (false οΌ b) β ((false οΌ b) β β₯)) (inr falseβ true) (inl false) y)
    x

isSet-π : isSet π
isSet-π = hedberg deceq-π
