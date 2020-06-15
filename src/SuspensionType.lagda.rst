::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom
   open import QuasiinverseType
   open import DecidableEquality
   open import NaturalType
   open import HLevelTypes
   open import HLevelLemmas
   open import HedbergLemmas

Suspensions
~~~~~~~~~~~

.. image:: _statics/images/suspension-type.png
  :target: _statics/images/suspension-type.png

::

   module SuspensionType where

     module S where

     private
       data Suspₚ {ℓ : Level} (A : Type ℓ) : Type ℓ where
         Nₚ : Suspₚ A
         Sₚ : Suspₚ A

       data Suspₓ {ℓ} (A : Type ℓ) : Type ℓ where
         mkSusp : Suspₚ A → (𝟙 ℓ → 𝟙 ℓ) → Suspₓ A

     Susp = Suspₓ

-  point-constructors

::

     North : ∀ {ℓ} {A : Type ℓ} → Susp A
     North = mkSusp Nₚ _

     South : ∀ {ℓ} {A : Type ℓ} → Susp A
     South = mkSusp Sₚ _

-  path-constructors

::

     postulate
       merid : ∀ {ℓ} {A : Type ℓ}
             → A
             → Path {ℓ}{Susp A} North South

Recursion principle on points

::

     Susp-rec
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{C : Type ℓ₂}
       → (cₙ cₛ  : C)
       → (merid' : A → cₙ == cₛ)
       ------------------------
       → (Susp A → C)

     Susp-rec cₙ _ _ (mkSusp Nₚ _) = cₙ
     Susp-rec _ cₛ _ (mkSusp Sₚ _) = cₛ

Recursion principle on paths

::

     postulate
       Susp-βrec
         : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{C : Type ℓ₂}
         → {cₙ cₛ : C} {mer : A → cₙ == cₛ}
         → {a : A}
         -------------------------------------------
         → ap (Susp-rec cₙ cₛ mer) (merid a) == mer a

Induction principle on points

::

     Susp-ind
       : ∀ {ℓ : Level} {A : Type ℓ} (C : Susp A → Type ℓ)
       → (N' : C North)
       → (S' : C South)
       → (merid' : (x : A) → N' == S' [ C ↓ (merid x) ])
       --------------------------------------------------
       → ((x : Susp A) → C x)

     Susp-ind _ N' S' _ (mkSusp Nₚ _) = N'
     Susp-ind _ N' S' _ (mkSusp Sₚ _) = S'

Induction principle on paths

::

     postulate
       Susp-βind
         : ∀ {ℓ} {A : Type ℓ} (C : Susp A → Type ℓ)
         → (N' : C North)
         → (S' : C South)
         → (merid' : (x : A) → N' == S' [ C ↓ (merid x)]) {x : A}
         --------------------------------------------------------
         → apd (Susp-ind C N' S' merid') (merid x) == merid' x
