::

   {-# OPTIONS --without-K --exact-split  --rewriting #-}
   open import TransportLemmas
   open import EquivalenceType

   open import HomotopyType
   open import FunExtAxiom
   open import HLevelTypes

Circles
~~~~~~~

The circle type is constructed by postulating a type with a single
element (base) and a nontrivial path (loop).

::

   module CircleType {ℓ : Level} where
     open import Rewriting

::

     postulate
       S¹ : Type ℓ
       base : S¹
       loop : base ≡ base

Recursion principle on points

::

     postulate
       S¹-rec
         : ∀ {ℓ : Level}
         → (A : Type ℓ)
         → (a : A)
         → (p : a ≡ a)
         --------------
         → (S¹ → A)

Recursion principle on paths

::

     postulate
       S¹-βrec-base
         : ∀ {ℓ : Level}
         → (A : Type ℓ)
         → (a : A)
         → (p : a ≡ a)
         ------------------------------
         → S¹-rec A a p base ↦ a

     {-# REWRITE S¹-βrec-base #-}

::

     postulate
       S¹-βrec-loop
         : ∀ {ℓ : Level}
         → (A : Type ℓ)
         → (a : A)
         → (p : a ≡ a)
         ------------------------------
         → ap (S¹-rec A a p) loop ↦ p

     {-# REWRITE S¹-βrec-loop #-}

Induction principle on points

::

     postulate
       S¹-ind
         : ∀ {ℓ : Level}
         → {P : S¹ → Type ℓ}
         → (x : P base)
         → (x == x [ P ↓ loop ])
         -----------------------
         → ((t : S¹) → P t)

::

     postulate
       S¹-βind-base
         : ∀ {ℓ : Level}
         → {P : S¹ → Type ℓ}
         → (x : P base)
         → (p : x == x [ P ↓ loop ])
         ---------------------------
         → S¹-ind x p base ↦ x

     {-# REWRITE S¹-βind-base #-}

Induction principle on paths

::

     postulate
       S¹-βind-loop
         :  ∀ {ℓ : Level}
         → {P : S¹ → Type ℓ}
         → (x : P base)
         → (p : x == x [ P ↓ loop ])
         → apd (S¹-ind x p) loop ↦ p

     {-# REWRITE S¹-βind-loop #-}

::

     this-proofs-rewriting
         :  ∀ {ℓ : Level}
         → {P : S¹ → Type ℓ}
         → (x : P base)
         → (p : x == x [ P ↓ loop ])
         → apd (S¹-ind x p) loop ≡ p

     this-proofs-rewriting _ _ = idp
