::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas

Homotopies
----------

::

   module HomotopyType
     {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {P : A → Type ℓ₂}
     where

..

   In a type-theoretical sense, a homotopy between two functions is a
   family of equalities between their applications.

Let :math:`f , g : \prod_{(x:A)} P(x)` be two sections of a type family
:math:`P : A \to \mathcal{U}`. A **homotopy** from :math:`f` to
:math:`g` is a dependent function of type

.. math::  (f \sim g) :\equiv \prod_{(x : A)} (f(x) = g(x)). 

Homotopy types
~~~~~~~~~~~~~~

::

     homotopy
       : (f g : Π A P)
       ---------------
       → Type (ℓ₁ ⊔ ℓ₂)

     homotopy f g = ∀ (x : A) → f x == g x

Usual notation for homotopy:

::

     _∼_ : (f g : ((x : A) → P x)) → Type (ℓ₁ ⊔ ℓ₂)
     f ∼ g = homotopy f g

Homotopy is an equivalence relation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. raw:: html

   <!-- tabs:start -->

*Reflexivity*
^^^^^^^^^^^^^

::

     h-refl
       : (f : Π A P)
       -------------
       → f ∼ f

     h-refl f x = idp

*Symmetry*
^^^^^^^^^^

::

     h-sym
       : (f g : Π A P)
       → f ∼ g
       -------
       → g ∼ f

     h-sym _ _ e x = ! (e x)

*Transitivity*
^^^^^^^^^^^^^^

::

     h-comp
       : {f g h : Π A P}
       → f ∼ g
       → g ∼ h
       -------
       → f ∼ h

     h-comp u v x = (u x) · (v x)

.. raw:: html

   <!-- tabs:end -->

Syntax:

::

     _●_
       : {f g h : Π A P}
       → f ∼ g
       → g ∼ h
       -------
       → f ∼ h

     α ● β = h-comp α β
