::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom
   open import HLevelTypes

Intervals
~~~~~~~~~

Interval. An interval is defined by taking two points (two elements) and
a path between them (an element of the equality type). This path is
nontrivial.

::

   module IntervalType where

     private

       data !I : Type₀ where
         !Izero : !I
         !Ione : !I

     I : Type₀
     I = !I

     Izero : I
     Izero = !Izero

     Ione : I
     Ione = !Ione

     postulate
       seg : Izero == Ione

Recursion principle on points.

::

     I-rec
       : ∀ {ℓ : Level} {A : Type ℓ}
       → (a b : A)
       → (p : a == b)
       --------------
       → (I → A)

     I-rec a _ _ !Izero = a
     I-rec _ b _ !Ione  = b

Recursion principle on paths.

::

     postulate
       I-βrec
         : ∀ {ℓ : Level} (A : Type ℓ)
         → (a b : A)
         → (p : a == b)
         ---------------------------
         → ap (I-rec a b p) seg == p
