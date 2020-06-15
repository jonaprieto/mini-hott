::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom
   open import HLevelTypes
   open import MonoidType

Groups
~~~~~~

::

   module
     GroupType
       where

A group :math:`G` is a monoid with something else, *inverses* for each
element. This means, there is a function
:math:`\mathsf{inverse} : G → G` such that:

.. math::

   ∀ (x : G) → \mathsf{inverse}(x) <> x ≡ e\text {  and  }x <>
   \mathsf{inverse}(x)  ≡ e,

where :math:`G` is the group, :math:`e` the unit and :math:`<>` the
operation from the underlined monoid. This is the following type for
groups:

::

     Group
       : ∀ {ℓ : Level} → Type (lsuc ℓ)

     Group
       = ∑ (Monoid) (λ {(monoid G e _<>_ GisSet lunit runit assoc)
         → ∑ (G → G) (λ inverse →
           ∏ G (λ x →
             -- properties:
             (   (x <> inverse x) == e)
             × ( (inverse x <> x) == e ))
             )})
