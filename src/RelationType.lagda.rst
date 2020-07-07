::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType
   open import HLevelTypes


Relation
~~~~~~~~

::

   module RelationType where

     record Rel {ℓ : Level} (A : Type ℓ) : Type (lsuc ℓ) where
       field
         R     : A → A → Type ℓ
         Rprop : (a b : A) → isProp (R a b)
     open Rel {{...}} public
