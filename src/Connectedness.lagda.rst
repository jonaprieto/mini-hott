::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom
   open import HLevelTypes

   open import SetTruncationType

Connectedness
-------------

0-connected type
~~~~~~~~~~~~~~~~

::

   {-
   _is-0-connected
     : ∀ {ℓ : Level}
     → (A : Type ℓ)
     → Type ℓ

   A is-0-connected = isContr (∥ A ∥₀)
   -}
