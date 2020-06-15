::

   {-# OPTIONS --without-K --exact-split #-}

   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom
   open import HLevelTypes

Monoids
~~~~~~~

A **monoid** is a algebraic structure on a set with a featured object
called the *unit* and an associative binary operation (also called the
multiplication) that fulfills certain properties described below.

Before monoids, we could define instead a much simpler structure, the
magma. A **magma** is basically a set and an binary operation. Then, any
monoid is also magma, but magmas are not so interesting as the monoids.

::

   module
     MonoidType
       where

::

     record
       Monoid {ℓ : Level}
         : Type (lsuc ℓ)
         where
       constructor monoid
       field
         M   : Type ℓ       -- The carrier
         e   : M            -- Unit element (at least one element, this one)
         _⊕_ : M → M → M    -- Operation

         M-is-set : isSet M   -- the carrier is a set

         -- axioms:
         l-unit : (x : M) → (e ⊕ x) == x
         r-unit : (x : M) → (x ⊕ e) == x
         assoc  : (x y z : M) → (x ⊕ (y ⊕ z)) == ((x ⊕ y) ⊕ z)
