::

   {-# OPTIONS --without-K --exact-split --rewriting #-}
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

Propositional truncation
~~~~~~~~~~~~~~~~~~~~~~~~

Propositional truncation (or reflection) is the universal solution to
the problem of mapping :math:`X` to a proposition :math:`P`:

Notes:

-  It’s possible to extend MLTT to get truncations for all types. (Such
   as resizing + funext, or higher inductive types.)

For a different way of formalising trucation see:
`agda-premises <https://hub.darcs.net/gylterud/agda-premises/browse/Premises/Truncation.agda>`__.

::

   module
     TruncationType
     where

::

     private
       data
         !∥_∥ {ℓ} (A : Type ℓ)
           : Type ℓ
           where
           !∣_∣ : A → !∥ A ∥

::

     ∥_∥
       : ∀ {ℓ : Level} (A : Type ℓ)
       → Type ℓ

     ∥ A ∥ = !∥ A ∥

     prop-trunc = ∥_∥

::

     ∣_∣
       : ∀ {ℓ : Level} {X : Type ℓ}
       ------------
       → X → ∥ X ∥

     ∣ x ∣ = !∣ x ∣

::

     ∥∥-intro = ∣_∣

Any two elements of the truncated type are equal

{: .axiom}

::

     postulate
       trunc
         : ∀ {ℓ : Level} {A : Type ℓ}
         → isProp ∥ A ∥

Recursion principle

::

     trunc-rec
       :  ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{P : Type ℓ₂}
       → isProp P
       → (A → P)
       -----------
       → ∥ A ∥ → P

     trunc-rec _ f !∣ x ∣ = f x

::

     trunc-elim = trunc-rec
     ∥∥-rec     = trunc-rec

There exists the possibility to charactherize, propositional truncation
using an impredicative approach, which means, our definition will lay on
a larger universe as on the right-hand side in the following
formulation.

.. math::  ∥ X ∥ ⇔ ∏ (P : \mathsf{Type} ), \mathsf{isProp}(P) → (X → P) → P

Remarks:

-  rhs is a propositon assuming funext
-  this equation tells us an important relation (a pattern) between the
   type (in this case, prop-trunc) and its elimination principle
   (trunc-rec)
-  *Impredicative* means in this context: “it is defined in terms of
   quantification over a family which the thing we are defining is a
   member of.” (Gylterud).

Truncation Lemmas
^^^^^^^^^^^^^^^^^

::

     truncated-is-prop
       : ∀ {ℓ : Level} {A : Type ℓ}
       → isProp (∥ A ∥)

     truncated-is-prop = trunc

::

     ∥∥-is-prop    = truncated-is-prop
     trunc-is-prop = truncated-is-prop

::

     trunc-≃-prop
       : ∀ {ℓ : Level} {A : Type ℓ}
       → A is-prop
       -----------
       → ∥ A ∥ ≃ A

     trunc-≃-prop pA = lemma333 trunc pA (trunc-rec pA id) ∣_∣

A relation between double implication and the truncation of a type:

::

     postulate
      trunc-⇔-¬¬
        : ∀ {ℓ} {X : Type ℓ}
        → ∥ X ∥ ⇔ (¬ (¬ X))

Using propositional truncation, we are able to define properly the
logical disjunction and existence as follows.

::

     _∨_
       : ∀ {ℓ₁ ℓ₂ : Level}
       → (p : hProp ℓ₁) (q : hProp ℓ₂)
       → Type (ℓ₁ ⊔ ℓ₂)
     (P , _) ∨ (Q , _) = ∥ P + Q ∥

     infix 2 _∨_

Conjunction is the product of two mere propositons.

::

     _∧_
       : ∀ {ℓ₁ ℓ₂ : Level}
       → (p : hProp ℓ₁) (q : hProp ℓ₂)
       → Type (ℓ₁ ⊔ ℓ₂)

     (P , _) ∧ (Q , _) = P × Q

     infix  2 _∧_

::

     ∃[_]_
       : ∀ {ℓ : Level}
       → (T : Type ℓ) → (P : T → hProp ℓ)
       → Type ℓ

     ∃[ T ] P = ∥ ∑ T (λ x → π₁ (P x)) ∥

Another use of propositional truncation is to say a type :math:`A` is
non-empty. In this case, we have an element of :math:`∥A∥`

::

     _is-non-empty
       : ∀ {ℓ : Level}
       → (A : Type ℓ)
       → Type ℓ
     A is-non-empty = ∥ A ∥

     infixl 100 _is-non-empty

::

     is-non-empty-is-prop
       : ∀ {ℓ : Level}{A : Type ℓ}
       → isProp (A is-non-empty)

     is-non-empty-is-prop = ∥∥-is-prop

For any type :math:`A` and a term :math:`a : A`, we shall say the
connected commponent of :math:`a` is all the terms in :math:`A`
“connected” with :math:`a`.

::

     connected-component
       : ∀ {ℓ : Level} {A : Type ℓ}
       → (a : A)
       → Type ℓ

     connected-component {A = A} a = ∑ A (λ x → ∥ a ≡ x ∥ )

Consequently, two terms appear to be in the same component whenever
there is an element in ∥ x ≡ y ∥.

::

     _is-in-the-same-component-of_
       : ∀ {ℓ : Level}{A : Type ℓ}
       → (x y : A) → Type ℓ

     x is-in-the-same-component-of y = ∥ x ≡ y ∥

     infix 100 _is-in-the-same-component-of_

::

     _is-connected
       : ∀ {ℓ : Level} (A : Type ℓ)
       → Type ℓ

     A is-connected =
         (A is-non-empty)
       × ((x y : A) → (x is-in-the-same-component-of y))

::

     is-connected-is-prop
       : ∀ {ℓ : Level} {A : Type ℓ}
       ---------------------------
       → isProp (A is-connected)

     is-connected-is-prop =
       ×-is-prop
         is-non-empty-is-prop
         (pi-is-prop (λ x → pi-is-prop λ y → trunc-is-prop))
