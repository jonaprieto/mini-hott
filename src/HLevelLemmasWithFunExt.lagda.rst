::

   {-# OPTIONS --without-K --exact-split #-}
   module _ where

   open import TransportLemmas
   open import EquivalenceType

   open import ProductIdentities
   open import CoproductIdentities

   open import HomotopyType
   open import HomotopyLemmas

   open import HalfAdjointType
   open import QuasiinverseType
   open import QuasiinverseLemmas

   open import UnivalenceAxiom
   open import HLevelTypes
   open import HLevelLemmas

::

   module HLevelLemmasWithFunExt where


Propositions are propositions. This time, please notice the strong use
of function extensionality, used twice here.

::

     propIsProp
       : ∀ {ℓ : Level} {A : Type ℓ}
       → isProp (isProp A)

     propIsProp {_}{A} =
       λ x y → funext (λ a →
                 funext (λ b
                   → propIsSet x a b (x a b) (y a b)))
       where open import FunExtAxiom

::

     prop-is-prop-always = propIsProp
     prop-is-prop        = propIsProp
     prop→prop           = propIsProp
     isProp-isProp       = propIsProp
     is-prop-is-prop     = propIsProp

The dependent function type to proposition types is itself a
proposition.

::

     isProp-pi
       : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : A → Type ℓ₂}
       -- (funext : Function-Extensionality)
       → ((a : A) → isProp (B a))
       --------------------------
       → isProp ((a : A) → B a)

     isProp-pi props f g = funext λ a → props a (f a) (g a)
      where open import FunExtAxiom

::

     pi-is-prop = isProp-pi
     Π-isProp   = isProp-pi
     piIsProp   = isProp-pi

Propositional extensionality, here stated as ``prop-ext``, is a
consequence of univalence axiom.

::

     setIsProp
       : ∀ {ℓ : Level} {A : Type ℓ}
       -----------------
       → isProp (isSet A)

     setIsProp {ℓ} {A} p₁ p₂ =
       funext (λ x →
         funext (λ y →
           funext (λ p →
             funext (λ q → propIsSet (p₂ x y) p q (p₁ x y p q) (p₂ x y p q)))))
            where open import FunExtAxiom

::

     set-is-prop = setIsProp
     set→prop    = setIsProp
