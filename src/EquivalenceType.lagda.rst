Equivalences
------------

There are three definitions to say a function is an equivalence. All
these definitions are required to be mere propositions and to hold the
bi-implication of begin *quasi-inverse*. We show this clearly in what
follows. Nevertheless, we want to get the following fact:

::

   {-# OPTIONS --without-K --exact-split #-}
   open import BasicTypes
   open import HLevelTypes
   open import FibreType

   open import Transport
   open import HomotopyType

   module EquivalenceType where

.. math::  \mathsf{isContr}(f) \cong \mathsf{ishae}(f) \cong \mathsf{biinv}(f). 

Contractible maps
~~~~~~~~~~~~~~~~~

A map is *contractible* if the fiber in any point is contractible, that
is, each element has a unique preimagen.

::

   isContrMap
     : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
     → (f : A → B)
     → Type (ℓ₁ ⊔ ℓ₂)

   isContrMap {B = B} f = (b : B) → isContr (fib f b)

Synomyns:

::

   map-contractible = isContrMap
   _is-contr-map    = isContrMap

There exists an equivalence between two types if there exists a
contractible function between them.

::

   isEquiv
     : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}
     → (f : A → B)
     → Type (ℓ₁ ⊔ ℓ₂)

   isEquiv f = isContrMap f

Synomyms:

::

   isEquivalence   = isEquiv
   _is-equivalence = isEquiv
   _is-equiv       = isEquiv

Equivalence Type
~~~~~~~~~~~~~~~~

::

   _≃_
     : ∀ {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁)(B : Type ℓ₂)
     → Type (ℓ₁ ⊔ ℓ₂)

   A ≃ B = Σ (A → B) isEquiv

::

   module EquivalenceMaps {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁}{B : Type ℓ₂}  where

::

     lemap ≃-to-→ fun≃ _∙ _∙→ apply
       : A ≃ B
       -------
       → (A → B)

     lemap = π₁

More syntax:

::

     ≃-to-→ = lemap
     fun≃   = lemap
     _∙     = lemap
     _∙→    = lemap
     apply  = lemap

     infixl 70 _∙ _∙→

::

     remap ≃-to-← invfun≃ _∙← rapply
       : A ≃ B
       ---------
       → (B → A)

     remap (f , contrf) b = π₁ (π₁ (contrf b))

::

     ≃-to-←  = remap
     invfun≃ = remap
     _∙←     = remap
     rapply  = remap

     infixl 70 _∙←

The maps of an equivalence are inverses in particular

::

     lrmap-inverse ∙→∘∙←
       : (e : A ≃ B) → {b : B}
       -----------------------
       → (e ∙→) ((e ∙←) b) == b

     lrmap-inverse (f , eqf) {b} = fib-eq (π₁ (eqf b))

::

     ∙→∘∙← = lrmap-inverse

::

     rlmap-inverse ∙←∘∙→
       : (e : A ≃ B) → {a : A}
       ------------------------
       → (e ∙←) ((e ∙→) a) == a

     rlmap-inverse (f , eqf) {a} = ap π₁ ((π₂ (eqf (f a))) fib-image)

::

     ∙←∘∙→ = rlmap-inverse

::

     lrmap-inverse-h  ∙→∘∙←-h
       : (e : A ≃ B)
       ------------------------
       → ((e ∙→) ∘ (e ∙←)) ∼ id

     lrmap-inverse-h e = λ x → lrmap-inverse e {x}

::

     ∙→∘∙←-h = lrmap-inverse-h

::

     rlmap-inverse-h ∙←∘∙→-h
       : (e : A ≃ B)
       ------------------------
       → ((e ∙←) ∘ (e ∙→)) ∼ id

     rlmap-inverse-h e = λ x → rlmap-inverse e {x}

::

     ∙←∘∙→-h = rlmap-inverse-h

::

   open EquivalenceMaps public
