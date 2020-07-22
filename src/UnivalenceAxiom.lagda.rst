::

   {-# OPTIONS --without-K --exact-split #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import QuasiinverseType
   open import QuasiinverseLemmas

Voevodsky’s Univalence Axiom
----------------------------

Voevodsky’s Univalence axiom is postulated. It induces an equality
between any two equivalent types. Some :math:`β` and :math:`η` rules are
provided.

::

   module UnivalenceAxiom {ℓ : Level} {A B : Type ℓ} where

::

     idtoeqv
       : A == B
       --------
       → A ≃ B

     idtoeqv p =
       qinv-≃
         (coe p)
         ((!coe p) ,
           (coe-inv-l p , coe-inv-r p))

More syntax:

::

     ==-to-≃ = idtoeqv
     ≡-to-≃  = idtoeqv
     ite     = idtoeqv
     cast    = idtoeqv  -- Used in the Symmetry Book.

The **Univalence axiom** induces an equivalence between equalities and
equivalences.

Univalence Axiom.

::

     postulate
       axiomUnivalence
         : isEquivalence ≡-to-≃

In Slide 20 from an `Escardo’s
talk <https://www.newton.ac.uk/files/seminar/20170711100011001-1442677.pdf>`__,
base on what we saw, we give the following no standard definition of
Univalence axiom (without transport).

::

     open import HLevelTypes

     UA
       : ∀ {ℓ : Level}
       → (Type (lsuc ℓ))

     UA {ℓ = ℓ}  = (X : Type ℓ) → isContr (∑ (Type ℓ) (λ Y → (X ≃ Y)))

About this Univalence axiom version:

-  ∑ (Type ℓ) (λ Y → X ≃ Y) is inhabited, but we don’t know if it’s
   contractible unless, we demand (assume) to be propositional. Then, in
   such a case, we use the theorem (isProp P ≃ (P → isContr P)). To be
   more precise, we know it’s contractible, in fact, the center of
   contractibility, is indeed (X, id-≃ X : X ≃ X).

-  Univalence is a generalized extensionality axiom for intensional MLTT
   theory.

-  The type UA is a proposition.

-  UA is consistent with MLTT.

-  Theorem of MLTT+UA: :math:`P(X)` and :math:`X≃Y` imply :math:`P(Y)`
   for any :math:`P : \mathsf{Type} → \mathsf{Type}`.

-  Theorem of spartan MLTT with two universes. The univalence axiom
   formulated with crude isomorphism rather than equivalence is false!.

::

     eqvUnivalence
       : (A == B) ≃ (A ≃ B)

     eqvUnivalence = idtoeqv , axiomUnivalence

More syntax:

::

     ==-equiv-≃ = eqvUnivalence
     ==-≃-≃     = eqvUnivalence
     ≡-≃-≃      = eqvUnivalence

Introduction rule for equalities:

::

     ua
       : A ≃ B
       -------
       → A == B

     ua = remap eqvUnivalence

More syntax:

::

     ≃-to-==   = ua
     eqv-to-eq = ua

Computation rules

::

     ua-β idtoeqv-ua-β
       : (α : A ≃ B)
       ----------------------
       → idtoeqv (ua α) == α

     ua-β eqv = lrmap-inverse eqvUnivalence
     idtoeqv-ua-β = ua-β

::

     ua-η
       : (p : A == B)
       ---------------------
       → ua (idtoeqv p) == p

     ua-η p = rlmap-inverse eqvUnivalence
